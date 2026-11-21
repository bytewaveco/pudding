#!/usr/bin/env node
// Differential fuzzer. Generates random TypeScript functions inside the
// subset Pudding supports, runs each one in Node on every input of a small
// finite domain, and then asks Pudding about two laws per function:
//
//   A  the function returns exactly what Node returned, for every input
//   B  the same, with one result changed
//
// Law A is true unless some input makes the function throw; law B is always
// false. Pudding must never prove a false law. Proving A when it is true is
// expected too, and a failure to do so is reported as a disagreement unless
// Pudding refused the code as unsupported.
//
// With --unbounded the inputs are all bigints, a wide range of whole numbers,
// and so on, which Pudding proves with tactics instead of by evaluation. No
// table of results can be written for those, so each function is compared
// with a copy that has one constant or operator changed. When Node finds an
// input on which the two differ, the law "they are equal" is false and must
// not be proved.
//
//   node scripts/fuzz.mjs [--seed N] [--programs N] [--batch N] [--cross-check] [--unbounded]
//
// Run `npm run build` first. Programs that expose a problem are kept under
// .lab/fuzz/failures/.

import { spawnSync } from "node:child_process"
import { cpSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"
import { parseArgs } from "node:util"
import { locateLean } from "../dist/runner.js"

const root = dirname(dirname(fileURLToPath(import.meta.url)))
const { values: options } = parseArgs({
  options: {
    seed: { type: "string", default: "1" }, programs: { type: "string", default: "120" }, batch: { type: "string", default: "30" },
    "cross-check": { type: "boolean", default: false }, quiet: { type: "boolean", default: false }, unbounded: { type: "boolean", default: false }, keep: { type: "boolean", default: false },
  },
})

// ------------------------------------------------------------------ random

class Random {
  constructor(seed) {
    this.state = seed >>> 0
  }
  next() {
    this.state = (this.state + 0x6d2b79f5) | 0
    let t = Math.imul(this.state ^ (this.state >>> 15), 1 | this.state)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
  int(n) {
    return Math.floor(this.next() * n)
  }
  pick(items) {
    return items[this.int(items.length)]
  }
  chance(p) {
    return this.next() < p
  }
  sample(items, count) {
    const pool = [...items]
    const out = []
    while (out.length < count && pool.length) out.push(pool.splice(this.int(pool.length), 1)[0])
    return out
  }
}

// --------------------------------------------------------------- generator

const TYPES = ["bool", "big", "num", "str"]
const TS = { bool: "boolean", big: "bigint", num: "number", str: "string" }
const BIGS = [-7n, -3n, -1n, 0n, 1n, 2n, 5n, 10n]
const NUMS = [-4, -1, 0, 1, 2, 3, 7]
const STRS = ["", "a", "b", "ab", "x:y", "é", "😀", "A b", "0"]

const show = value => (typeof value === "bigint" ? `${value}n` : typeof value === "string" ? JSON.stringify(value) : String(value))
/** A literal as an expression, parenthesized so a leading minus cannot bind to what comes before. */
const literal = value => (typeof value === "bigint" || typeof value === "number" ? (value < 0 ? `(${show(value)})` : show(value)) : show(value))

class Scope {
  constructor(parent, boundary = false) {
    this.parent = parent
    this.boundary = boundary
    this.names = new Map()
    /** Outer names this scope has already read, which it therefore must not redeclare. */
    this.read = new Set()
  }
  lookup(name) {
    return this.names.get(name) ?? this.parent?.lookup(name)
  }
  /** Every visible entry, innermost declaration winning. */
  visible() {
    const seen = new Map()
    for (let scope = this, crossed = false; scope; crossed ||= scope.boundary, scope = scope.parent) {
      for (const [name, entry] of scope.names) if (!seen.has(name)) seen.set(name, { ...entry, name, outside: crossed })
    }
    return [...seen.values()]
  }
  /** Record that a name declared further out was read from here. */
  noteRead(name) {
    for (let scope = this; scope && !scope.names.has(name); scope = scope.parent) {
      scope.read.add(name)
      // A closure may legally mention a name its enclosing block declares later,
      // unless it is called on the spot, which TypeScript checks like inline code.
      if (scope.boundary && !scope.immediate) return
    }
  }
}

class Generator {
  constructor(random, index) {
    this.random = random
    this.index = index
    this.counter = 0
    this.tables = []
  }

  fresh(scope, type, prefix = "v") {
    const r = this.random
    // Reusing an outer name is what exercises shadowing. Keeping its type means a
    // closure that already mentions the name still type-checks against the new one.
    if (r.chance(0.3)) {
      const outer = scope.visible().filter(e => !scope.names.has(e.name) && !scope.read.has(e.name) && e.kind === "var" && !e.fixed && e.type === type)
      if (outer.length) return r.pick(outer).name
    }
    return `${prefix}${this.counter++}`
  }

  value(type) {
    const r = this.random
    return type === "bool" ? r.chance(0.5) : type === "big" ? r.pick(BIGS) : type === "num" ? r.pick(NUMS) : r.pick(STRS)
  }

  /** An expression of the given type. */
  expr(type, scope, depth) {
    const r = this.random
    const leaf = () => {
      // A closure reads a reassigned variable of an enclosing function as it is when the closure is called.
      const far = r.chance(0.5)
      const candidates = scope.visible().filter(e => e.kind === "var" && e.type === type && (far || !(e.outside && e.mutable)))
      if (candidates.length && r.chance(0.75)) {
        const chosen = r.pick(candidates)
        scope.noteRead(chosen.name)
        return chosen.name
      }
      return `(${literal(this.value(type))} as ${TS[type]})`
    }
    // What an object or a list holds right now, which depends on every change made to it so far, through any name.
    const stored = scope.visible().filter(e => (e.kind === "box" || e.kind === "list" || e.kind === "holder" || e.kind === "queue") && e.type === type)
    if (stored.length && r.chance(0.3)) {
      const chosen = r.pick(stored)
      scope.noteRead(chosen.name)
      const part = r.pick(["v", "w"])
      const position = r.chance(0.5) ? "0" : `${chosen.name}.length - 1`
      return chosen.kind === "box" ? `${chosen.name}.${part}`
        : chosen.kind === "holder" ? `${chosen.name}.box.${part}`
        : chosen.kind === "queue" ? `${chosen.name}[${position}]!.${part}`
        : `${chosen.name}[${position}]!`
    }
    if (depth <= 0 || r.chance(0.2)) return leaf()
    const sub = t => this.expr(t, scope, depth - 1)
    const calls = scope.visible().filter(e => e.kind === "fn" && e.type === type && e.ready && !e.busy)
    const choices = []
    const add = (weight, make) => choices.push([weight, make])
    add(2, leaf)
    add(1, () => `(${sub("bool")} ? ${sub(type)} : ${sub(type)})`)
    add(1, () => `({ p: ${sub(type)}, q: ${sub(r.pick(TYPES))} }).p`)
    add(0.6, () => `[${sub(type)}, ${sub(type)}][${r.int(2)}]!`)
    add(0.5, () => `({ ...{ p: ${sub(type)}, q: ${sub(type)} }, q: ${sub(type)} }).${r.pick(["p", "q"])}`)
    add(0.5, () => `({ p: ${sub(type)}, ...(${sub("bool")} ? { p: ${sub(type)} } : null) }).p`)
    add(0.5, () => `(Object.assign({}, { p: ${sub(type)} }, ${sub("bool")} ? { p: ${sub(type)} } : null)).p`)
    add(0.5, () => {
      const from = r.pick(TYPES)
      const inner = new Scope(scope, true)
      inner.immediate = true
      const name = `a${this.counter++}`
      inner.names.set(name, { kind: "var", type: from })
      return `((${name}: ${TS[from]}): ${TS[type]} => ${this.expr(type, inner, depth - 1)})(${sub(from)})`
    })
    if (calls.length) {
      add(2.5, () => {
        const fn = r.pick(calls)
        scope.noteRead(fn.name)
        const count = fn.optional && r.chance(0.4) ? fn.params.length - 1 : fn.params.length
        const args = fn.params.slice(0, count).map(sub)
        // An explicit undefined takes the default too.
        if (fn.optional && count === fn.params.length && r.chance(0.25)) args[count - 1] = "undefined"
        return `${fn.name}(${args.join(", ")})`
      })
    }
    // A predicate over one element of a list, with the element in scope.
    const predicate = t => {
      const inner = new Scope(scope, true)
      const name = `e${this.counter++}`
      inner.names.set(name, { kind: "var", type: t })
      return `${name} => ${this.expr("bool", inner, depth - 1)}`
    }
    // A value that may be undefined or null, and what stands in for it.
    const maybe = t => r.pick([
      () => `(${sub("bool")} ? ${sub(t)} : undefined)`,
      () => `(${sub("bool")} ? ${sub(t)} : null)`,
      () => `(${sub("bool")} ? { p: ${sub(t)} } : undefined)?.p`,
      () => `(${sub("bool")} ? { p: ${sub(t)} } : null)?.p`,
      () => `({ p: ${sub(t)} } as { p: ${TS[t]}; q?: ${TS[t]} }).${r.pick(["p", "q"])}`,
      () => `[${sub(t)}, ${sub(t)}].${r.pick(["find", "findLast"])}(${predicate(t)})`,
      () => `[${sub(t)}, ${sub(t)}].at(${r.pick([-3, -1, 0, 1, 2])})`,
      () => `new Map<string, ${TS[t]}>([[${sub("str")}, ${sub(t)}], [${sub("str")}, ${sub(t)}]]).get(${sub("str")})`,
    ])()
    add(1.2, () => `(${maybe(type)} ?? ${sub(type)})`)
    add(0.6, () => `[${sub(type)}, ${sub(type)}].concat([${sub(type)}]).toReversed()[${r.int(3)}]!`)
    add(0.5, () => `([[${sub(type)}], [${sub(type)}, ${sub(type)}]].flat(${r.pick(["", "1", "Infinity"])}) as ${TS[type]}[])[${r.int(3)}]!`)
    add(0.5, () => `[${sub(type)}, ${sub(type)}].with(${r.pick([-2, -1, 0, 1])}, ${sub(type)})[${r.int(2)}]!`)
    add(0.5, () => `[${sub(type)}, ${sub(type)}, ${sub(type)}].toSpliced(${r.pick([0, 1, -1])}, ${r.pick([0, 1, -1])}, ${sub(type)})[${r.int(2)}]!`)
    add(0.4, () => `(Object.fromEntries([["a", ${sub(type)}], ["b", ${sub(type)}]]) as { a: ${TS[type]}; b: ${TS[type]} }).${r.pick(["a", "b"])}`)
    // TypeScript rejects a literal as the left side, so the value goes through a call.
    const opaque = t => `call((): ${TS[t]} => ${sub(t)})`
    if (type !== "bool") add(0.8, () => `(${opaque(type)} ${r.pick(["||", "&&"])} ${sub(type)})`)
    add(0.5, () => `(${maybe(type)} || ${sub(type)})`)
    const table = this.tables.find(t => !t.list && t.type === type && scope.lookup(t.key))
    if (table) add(1.5, () => `${table.name}[${table.key}]`)
    const listTable = this.tables.find(t => t.list && scope.lookup(t.key))
    if (listTable && type === "bool") add(1.5, () => `${listTable.name}[${listTable.key}].includes(${sub(listTable.type)})`)
    if (type === "bool") {
      const cmp = r.pick(["big", "num"])
      add(2, () => `(!${sub("bool")})`)
      // Zero, the empty string and undefined count as false; everything else as true.
      add(1, () => `(!${opaque(r.pick(["big", "num", "str"]))})`)
      add(0.8, () => {
        const t = r.pick(TYPES)
        return `(${maybe(t)} ${r.pick(["===", "!=="])} ${r.pick(["undefined", "null"])})`
      })
      add(0.6, () => `(typeof ${maybe(r.pick(TYPES))} === ${JSON.stringify(r.pick(["undefined", "object", "boolean", "bigint", "number", "string"]))})`)
      add(0.5, () => `(${JSON.stringify(r.pick(["a", "b", "c"]))} in { a: ${sub("big")}, b: ${sub("str")} })`)
      add(0.5, () => `Object.hasOwn({ a: ${sub("big")}, "0": ${sub("str")} }, ${JSON.stringify(r.pick(["a", "0", "z"]))})`)
      add(0.4, () => `Array.isArray(${r.pick([`[${sub("big")}]`, `{ a: ${sub("big")} }`, `new Map().keys()`])})`)
      add(0.4, () => `Boolean(${maybe(r.pick(TYPES))})`)
      add(0.4, () => `Number.${r.pick(["isInteger", "isFinite", "isNaN", "isSafeInteger"])}(${r.pick([sub("num"), "Infinity", "-Infinity"])})`)
      add(0.5, () => `("pre_" + ${sub("str")}).startsWith(${JSON.stringify(r.pick(["pre_", "pr", "x"]))})`)
      add(0.5, () => `(${sub("str")} + "_end").endsWith(${JSON.stringify(r.pick(["_end", "nd", "x"]))})`)
      add(0.5, () => `(${sub("str")} + "MID" + ${sub("str")}).includes("MID")`)
      add(0.6, () => `(${sub("num")} ${r.pick(["<", "<=", ">", ">="])} (${maybe("num")} ?? ${r.pick(["Infinity", "-Infinity"])}))`)
      add(0.6, () => {
        const t = r.pick(["big", "num", "str"])
        return `new Set([${sub(t)}, ${sub(t)}]).has(${sub(t)})`
      })
      add(0.5, () => {
        const t = r.pick(["big", "num", "str"])
        return `new Set([${sub(t)}]).${r.pick(["isSubsetOf", "isSupersetOf", "isDisjointFrom"])}(new Set([${sub(t)}, ${sub(t)}]))`
      })
      add(0.4, () => {
        const a = r.sample(STRS, 2).map(literal)
        const b = r.sample(STRS, 2).map(literal)
        return `new Set([${a.join(", ")}]).${r.pick(["union", "intersection", "difference", "symmetricDifference"])}(new Set([${b.join(", ")}])).has(${literal(r.pick(STRS))})`
      })
      add(0.5, () => `(() => { try { if (${sub("bool")}) throw new Error("x"); return true } catch { return false } })()`)
      add(0.5, () => {
        const t = r.pick(["big", "num", "str"])
        return `(() => { const m = new Map([[${sub(t)}, 1n], [${sub(t)}, 2n]]); return m.delete(${sub(t)}) })()`
      })
      add(0.4, () => `new Set<number | bigint>([${sub("num")}, ${sub("big")}]).has(${sub(r.pick(["num", "big"]))})`)
      add(2, () => `(${sub("bool")} ${r.pick(["&&", "||"])} ${sub("bool")})`)
      add(3, () => {
        const t = r.pick(TYPES)
        return `((${sub(t)} as ${TS[t]}) ${r.pick(["===", "!=="])} (${sub(t)} as ${TS[t]}))`
      })
      add(3, () => `(${sub(cmp)} ${r.pick(["<", "<=", ">", ">="])} ${sub(cmp)})`)
      // A number and a bigint are never equal, whatever their values.
      add(0.8, () => `((${sub("num")} as number | bigint) ${r.pick(["===", "!=="])} (${sub("big")} as number | bigint))`)
      add(0.8, () => `([${sub("num")}, ${sub("big")}, ${sub("num")}] as (number | bigint)[]).includes(${sub(r.pick(["num", "big"]))} as number | bigint)`)
      add(1.5, () => {
        const t = r.pick(TYPES)
        return `[${sub(t)}, ${sub(t)}, ${sub(t)}].includes(${sub(t)})`
      })
      add(1, () => {
        const t = r.pick(["big", "num"])
        const inner = new Scope(scope, true)
        const name = `e${this.counter++}`
        inner.names.set(name, { kind: "var", type: t })
        return `[${sub(t)}, ${sub(t)}].${r.pick(["some", "every"])}(${name} => ${this.expr("bool", inner, depth - 1)})`
      })
    } else if (type === "big") {
      add(4, () => `(${sub("big")} ${r.pick(["+", "-", "*"])} ${sub("big")})`)
      add(1, () => `(-${sub("big")})`)
      add(2, () => `(${sub("big")} ${r.pick(["/", "%"])} ${literal(r.pick(BIGS.filter(v => v !== 0n && v !== 1n)))})`)
      add(0.4, () => `(${sub("big")} ${r.pick(["/", "%"])} ${sub("big")})`)
      add(0.7, () => `BigInt(${sub("num")})`)
      add(1, () => `[${sub("big")}, ${sub("big")}, ${sub("big")}].${r.pick(["reduce", "reduceRight"])}((s, e) => s ${r.pick(["+", "-", "*"])} e, ${sub("big")})`)
      add(0.6, () => `[${sub("big")}, ${sub("big")}, ${sub("big")}].${r.pick(["reduce", "reduceRight"])}((s, e) => s ${r.pick(["+", "-"])} e)`)
      add(0.8, () => `[${sub("big")}, ${sub("big")}, ${sub("big")}].filter(${predicate("big")}).reduce((s, e) => s + e, ${sub("big")})`)
      add(0.5, () => `[${sub("big")}, ${sub("big")}].flatMap(e => (${sub("bool")} ? [e, ${sub("big")}] : [])).reduce((s, e) => s - e, ${sub("big")})`)
    } else if (type === "num") {
      add(4, () => `(${sub("num")} ${r.pick(["+", "-", "*"])} ${sub("num")})`)
      add(1, () => `(-${sub("num")})`)
      add(1.5, () => `(${sub("num")} % ${literal(r.pick(NUMS.filter(v => v !== 0)))})`)
      add(0.3, () => `(${sub("num")} % ${sub("num")})`)
      add(2, () => `Math.${r.pick(["floor", "trunc", "ceil"])}(${sub("num")} / ${literal(r.pick(NUMS.filter(v => v !== 0)))})`)
      add(1.5, () => `Math.${r.pick(["abs", "sign"])}(${sub("num")})`)
      add(1.5, () => `Math.${r.pick(["min", "max"])}(${sub("num")}, ${sub("num")})`)
      add(0.6, () => `(Math.${r.pick(["min", "max"])}(${sub("num")}, ${r.pick(["Infinity", "-Infinity"])}) === Infinity ? 1 : Math.${r.pick(["min", "max"])}(${sub("num")}, ${sub("num")}))`)
      add(0.8, () => {
        const t = r.pick(TYPES)
        return `[${sub(t)}, ${sub(t)}, ${sub(t)}].${r.pick(["indexOf", "lastIndexOf"])}(${sub(t)}${r.chance(0.5) ? `, ${r.pick([-2, 0, 1, 2, "undefined"])}` : ""})`
      })
      add(0.7, () => `[${sub("big")}, ${sub("big")}, ${sub("big")}].${r.pick(["findIndex", "findLastIndex"])}(${predicate("big")})`)
      add(0.6, () => `([10, 20, 30].at(${sub("num")}) ?? -1)`)
      add(0.6, () => `(() => { const m = new Map([[${sub("str")}, 1], [${sub("str")}, 2]]); m.delete(${sub("str")}); return m.size })()`)
      add(0.7, () => `Number(${sub("big")})`)
      // A half rounds upward, whatever its sign.
      add(1.5, () => `Math.round(${sub("num")} / ${literal(r.pick(NUMS.filter(v => v !== 0)))})`)
      add(0.7, () => {
        const t = r.pick(TYPES)
        return `new Set([${sub(t)}, ${sub(t)}, ${sub(t)}]).size`
      })
      add(0.7, () => `[${sub("big")}, ${sub("big")}, ${sub("big")}].filter(${predicate("big")}).length`)
      add(0.5, () => {
        const values = r.sample(NUMS, 3)
        return `[${values.map(literal).join(", ")}].sort((x, y) => ${r.pick(["x - y", "y - x", "Math.abs(x) - Math.abs(y)"])})[${r.int(3)}]!`
      })
      add(0.7, () => `[${sub(r.pick(TYPES))}, ${sub("bool")}].length`)
      if (listTable) add(1, () => `${listTable.name}[${listTable.key}].length`)
    } else {
      add(3, () => `(${sub("str")} + ${sub("str")})`)
      add(3, () => {
        const t = r.pick(["str", "big", "num"])
        return `\`${r.pick(["", "<", "n="])}\${${sub(t)}}${r.pick(["", ">", ":"])}\${${sub("str")}}\``
      })
      add(1, () => `String(${sub(r.pick(["big", "num"]))})`)
      // Padding depends on the length of the text, which for a number depends on its size and sign.
      add(1.2, () => `${r.chance(0.7) ? `String(${sub(r.pick(["big", "num"]))})` : leaf()}.${r.pick(["padStart", "padEnd"])}(${r.int(6)}${r.chance(0.8) ? `, ${JSON.stringify(r.pick(["0", " ", "ab", "x.y", ""]))}` : ""})`)
      add(1, () => `(${sub(r.pick(["big", "num"]))}).toString()`)
      add(0.8, () => `[${sub("big")}, ${r.pick(["null", "undefined", sub("str")])}, ${sub("num")}].join(${r.pick(["", '":"', "undefined", "null as unknown as string"])})`)
      add(0.7, () => `Object.keys({ z: 1, "2": 2, a: 3, "0": 4 }).join(",")`)
      add(0.7, () => `${JSON.stringify(r.pick(["  Ada-ok  ", "ababa", "hello"]))}.${r.pick(['trim()', 'toUpperCase()', 'toLowerCase()', 'slice(1, 4)', 'replace("a", "X")', 'replaceAll("a", "X")', 'split("-").join(":")'])}`)
    }
    const total = choices.reduce((sum, [weight]) => sum + weight, 0)
    let roll = r.next() * total
    for (const [weight, make] of choices) if ((roll -= weight) < 0) return make()
    return leaf()
  }

  /** Statements for a block. `context.returns` is the type the enclosing function returns. */
  block(scope, context, depth, length) {
    const r = this.random
    const lines = []
    // Functions are hoisted, so a block's statements may call one before its declaration is reached.
    const helpers = []
    if (depth > 0 && r.chance(0.5)) {
      const count = 1 + r.int(2)
      for (let i = 0; i < count; i++) {
        // Redeclaring an outer function in a block makes every call in the block mean the inner one, even before its declaration.
        const outer = scope.visible().filter(e => e.kind === "fn" && !scope.names.has(e.name) && !e.special)
        const shadowed = outer.length && r.chance(0.35) ? r.pick(outer) : undefined
        const params = shadowed ? shadowed.params : Array.from({ length: r.int(3) }, () => r.pick(TYPES))
        const helper = {
          kind: "fn", name: shadowed ? shadowed.name : `h${this.counter++}`, type: shadowed ? shadowed.type : r.pick(TYPES), params,
          optional: shadowed ? shadowed.optional : params.length > 0 && r.chance(0.3), at: r.int(length + 1),
          ready: shadowed ? true : r.chance(0.5),
          // A body generated last can read anything the block declares, including what is declared after a call to it.
          late: r.chance(0.35),
        }
        scope.names.set(helper.name, helper)
        helpers.push(helper)
      }
    }
    const helperText = helper => {
      const inner = new Scope(scope, true)
      const names = helper.params.map(() => `a${this.counter++}`)
      helper.busy = true
      const signature = names.map((name, i) => {
        // A default may use the parameters before it, never itself.
        const fallback = helper.optional && i === names.length - 1 ? ` = ${this.expr(helper.params[i], inner, 1)}` : ""
        inner.names.set(name, { kind: "var", type: helper.params[i], mutable: r.chance(0.2) })
        return `${name}: ${TS[helper.params[i]]}${fallback}`
      })
      const body = this.block(inner, { returns: helper.type, loop: false }, depth - 1, 1 + r.int(3))
      const text = [`function ${helper.name}(${signature.join(", ")}): ${TS[helper.type]} {`, ...body.map(l => "  " + l), `  return ${this.expr(helper.type, inner, 2)}`, "}"]
      helper.busy = false
      helper.ready = true
      return text
    }
    const emitHelpers = position => {
      for (const helper of helpers.filter(h => h.at === position)) {
        if (helper.late) lines.push(helper)
        else lines.push(...helperText(helper))
      }
    }
    for (let i = 0; i < length; i++) {
      emitHelpers(i)
      lines.push(...this.statement(scope, context, depth))
    }
    emitHelpers(length)
    return lines.flatMap(line => (typeof line === "string" ? [line] : helperText(line)))
  }

  statement(scope, context, depth) {
    const r = this.random
    const nested = (extra = {}) => this.block(new Scope(scope), { ...context, ...extra }, depth - 1, 1 + r.int(3)).map(l => "  " + l)
    const choices = []
    const add = (weight, make) => choices.push([weight, make])
    add(4, () => {
      const type = r.pick(TYPES)
      const value = this.expr(type, scope, 3)
      const name = this.fresh(scope, type)
      const mutable = r.chance(0.4)
      scope.names.set(name, { kind: "var", type, mutable })
      return [`${mutable ? "let" : "const"} ${name}: ${TS[type]} = ${value}`]
    })
    // A function may assign to a variable of the function it is declared in.
    const reach = r.chance(0.5)
    const assignable = scope.visible().filter(e => e.kind === "var" && e.mutable && (reach || !e.outside))
    if (assignable.length) {
      add(4, () => {
        const target = r.pick(assignable)
        scope.noteRead(target.name)
        const value = this.expr(target.type, scope, 2)
        if (target.type === "big" || target.type === "num") {
          if (r.chance(0.2)) return [`${target.name}${r.pick(["++", "--"])}`]
          // Repeated multiplication of numbers would leave the range a double holds exactly.
          const operators = target.type === "num" || context.loop ? ["=", "+=", "-="] : ["=", "+=", "-=", "*="]
          return [`${target.name} ${r.pick(operators)} ${value}`]
        }
        return [`${target.name} ${target.type === "str" && !context.loop ? r.pick(["=", "+="]) : "="} ${value}`]
      })
    }
    add(1, () => [`if (${this.expr("bool", scope, 2)}) return ${this.expr(context.returns, scope, 2)}`])
    add(0.25, () => [`if (${this.expr("bool", scope, 2)}) throw new Error("refused")`])
    if (context.loop) add(1.2, () => [`if (${this.expr("bool", scope, 2)}) ${r.pick(["break", "continue"])}`])
    if (depth > 0) {
      add(2.5, () => {
        const lines = [`if (${this.expr("bool", scope, 2)}) {`, ...nested(), "}"]
        if (r.chance(0.5)) lines.push("else {", ...nested(), "}")
        return lines
      })
      add(0.8, () => ["{", ...nested(), "}"])
      add(1.5, () => {
        const type = r.pick(TYPES)
        const inner = new Scope(scope)
        // The list is generated first, through the loop's scope, so the loop variable never takes a name the list reads.
        const items = Array.from({ length: 1 + r.int(3) }, () => this.expr(type, inner, 2))
        // Sometimes the list itself depends on a condition, and its two forms differ in length.
        const list = r.chance(0.3)
          ? `(${this.expr("bool", inner, 2)} ? [${items.join(", ")}] : [${items.slice(1).join(", ")}])`
          : `[${items.join(", ")}]`
        const name = this.fresh(inner, type, "x")
        inner.names.set(name, { kind: "var", type })
        const body = this.block(inner, { ...context, loop: true }, depth - 1, 1 + r.int(3))
        return [`for (const ${name} of ${list}) {`, ...body.map(l => "  " + l), "}"]
      })
      add(1, () => {
        const inner = new Scope(scope)
        const name = `i${this.counter++}`
        inner.names.set(name, { kind: "var", type: "num", fixed: true })
        const body = this.block(inner, { ...context, loop: true }, depth - 1, 1 + r.int(2))
        return [`for (let ${name} = 0; ${name} < ${r.int(4)}; ${name}++) {`, ...body.map(l => "  " + l), "}"]
      })
      add(1.2, () => {
        const type = r.pick(["big", "num", "str", "bool"])
        const labels = type === "bool" ? [true, false] : r.sample(type === "big" ? BIGS : type === "num" ? NUMS : STRS, 1 + r.int(3))
        const lines = [`switch (${this.expr(type, scope, 2)} as ${TS[type]}) {`]
        // Some switches have no break at all, so every clause falls into the next.
        const breaks = r.chance(0.3) ? 0 : 0.7
        for (const label of labels) {
          lines.push(`  case ${show(label)}: {`, ...nested({ loop: false }).map(l => "  " + l), "  }")
          if (r.chance(breaks)) lines.push("  break")
        }
        if (r.chance(0.6)) lines.push("  default: {", ...nested({ loop: false }).map(l => "  " + l), "  }")
        lines.push("}")
        return lines
      })
      add(0.8, () => {
        const [first, second] = [r.pick(TYPES), r.pick(TYPES)]
        const [left, right] = [this.expr(first, scope, 2), this.expr(second, scope, 2)]
        const [a, b] = [this.fresh(scope, first), `d${this.counter++}`]
        const line = r.chance(0.5)
          ? `const { p: ${a}, q: ${b} } = { p: ${left}, q: ${right} }`
          : `const [${a}, ${b}]: [${TS[first]}, ${TS[second]}] = [${left}, ${right}]`
        scope.names.set(a, { kind: "var", type: first })
        scope.names.set(b, { kind: "var", type: second })
        return [line]
      })
    }
    const outerValues = scope.visible().filter(e => e.kind === "var" && !e.mutable && !e.fixed)
    // The returned value is a literal: the block redeclares a name, so nothing in it may read that name directly.
    const probe = (call, type) => `if ((${call} as ${TS[type]}) === (${literal(this.value(type))} as ${TS[type]})) return (${literal(this.value(context.returns))} as ${TS[context.returns]})`
    if (outerValues.length) {
      // A closure over an outer name, in a block that then declares the same name.
      add(1.3, () => {
        const target = r.pick(outerValues)
        const type = target.type
        const g = `g${this.counter++}`
        const lines = [r.chance(0.5) ? `  const ${g} = (): ${TS[type]} => ${target.name}` : `  function ${g}(): ${TS[type]} { return ${target.name} }`]
        if (r.chance(0.4)) lines.push("  " + probe(r.chance(0.5) ? `${g}()` : `call(${g})`, type))
        lines.push(`  const ${target.name}: ${TS[type]} = ${literal(this.value(type))}`)
        if (r.chance(0.8)) lines.push("  " + probe(`${g}()`, type))
        return ["{", ...lines, "}"]
      })
      // A default that closes over an outer name which the body also declares.
      add(0.6, () => {
        const target = r.pick(outerValues)
        const name = `h${this.counter++}`
        scope.names.set(name, { kind: "fn", name, type: target.type, params: ["bool"], optional: false, ready: true, special: true })
        return [`function ${name}(flag: boolean, read = (): ${TS[target.type]} => ${target.name}): ${TS[target.type]} {`,
          `  const ${target.name}: ${TS[target.type]} = ${literal(this.value(target.type))}`, `  return flag ? read() : ${target.name}`, "}"]
      })
      // A default that mentions the name of the parameter after it.
      add(0.4, () => {
        const target = r.pick(outerValues)
        const name = `h${this.counter++}`
        scope.names.set(name, { kind: "fn", name, type: target.type, params: [target.type], optional: true, ready: true, special: true })
        return [`function ${name}(first: ${TS[target.type]} = call((): ${TS[target.type]} => ${target.name}), ${target.name}: ${TS[target.type]} = ${literal(this.value(target.type))}): ${TS[target.type]} {`,
          `  return first`, "}"]
      })
      // A loop whose list is computed by a closure over the loop variable's own name.
      add(0.3, () => {
        const target = r.pick(outerValues)
        return [`if (${this.expr("bool", scope, 2)}) {`, `  for (const ${target.name} of [call((): ${TS[target.type]} => ${target.name})]) { }`, "}"]
      })
    }
    // A running value changed inside a switch that falls through, or by a loop over a list
    // that depends on a condition, itself inside an `if` that nothing leaves early.
    add(1.5, () => {
      const type = r.pick(["big", "num"])
      const m = `m${this.counter++}`
      const update = () => `${m} ${r.pick(["+=", "-="])} ${this.expr(type, scope, 1)}`
      const lines = [`let ${m}: ${TS[type]} = ${literal(this.value(type))}`, `if (${this.expr("bool", scope, 2)}) {`]
      const inputs = scope.visible().filter(e => e.kind === "var" && e.domain && e.type !== "bool")
      if (inputs.length && r.chance(0.6)) {
        // Switch on an input, with labels it can actually take.
        const subject = r.pick(inputs)
        const labels = r.sample(subject.domain, 2)
        scope.noteRead(subject.name)
        lines.push(`  switch (${subject.name} as ${TS[subject.type]}) {`, `    case ${show(labels[0])}:`, `      ${update()}`)
        if (labels[1] !== undefined) lines.push(`    case ${show(labels[1])}:`, `      ${update()}`)
        if (r.chance(0.4)) lines.push("    default:", `      ${update()}`)
        lines.push("  }")
      } else {
        const items = [this.expr(type, scope, 1), this.expr(type, scope, 1)]
        const x = `x${this.counter++}`
        lines.push(`  for (const ${x} of (${this.expr("bool", scope, 2)} ? [${items.join(", ")}] : [${items[0]}])) ${m} += ${x}`)
      }
      lines.push("}")
      scope.names.set(m, { kind: "var", type, mutable: true })
      // Make the outcome depend on the running value.
      lines.push(`if ((${m} as ${TS[type]}) === (${literal(this.value(type))} as ${TS[type]})) return ${this.expr(context.returns, scope, 1)}`)
      return lines
    })
    // A function called in the middle of an expression changes what the rest of the expression
    // reads: a list that is being spread, filtered or mapped, or the variable being assigned to.
    add(1.2, () => {
      const [l, g, k] = [`l${this.counter++}`, `g${this.counter++}`, `k${this.counter++}`]
      const value = () => this.expr("big", scope, 1)
      // Growing the list is left to the uses that read its length once, or they would never end.
      const grows = r.chance(0.5)
      const effect = grows ? `${l}.push(${value()})` : `${l}[${r.int(2)}] = ${value()}`
      const uses = [
        `[...${l}, ${g}(), ...${l}]`,
        `${l}.filter(e => ${g}() !== e)`,
        `${l}.flatMap(e => (${g}() === e ? ${l} : [e, ...${l}]))`,
        `${l}.map(e => e + ${g}())`,
        `[${g}(), ...${l}].map((e, i) => e - (${l}[i] ?? ${value()}))`,
        `[${l}.length === ${2 + r.int(2)} ? ${g}() : ${value()}, ${l}.at(-1) ?? ${value()}, ...${l}]`,
      ]
      if (!grows) uses.push(`Array.from(${l}, e => e - ${g}())`)
      const lines = [
        `const ${l}: bigint[] = [${value()}, ${value()}]`,
        `const ${g} = (): bigint => { ${effect}; return ${value()} }`,
        `const ${k}: bigint = ${r.pick(uses)}.reduce((s, e) => s * 3n + e, ${value()})`,
      ]
      scope.names.set(k, { kind: "var", type: "big", mutable: false })
      return lines
    })
    add(0.8, () => {
      const type = r.pick(["big", "num"])
      const [t, b] = [`t${this.counter++}`, `b${this.counter++}`]
      const value = () => (type === "num" ? literal(this.value("num")) : this.expr("big", scope, 1))
      const lines = [
        `let ${t}: ${TS[type]} = ${value()}`,
        `const ${b} = (): ${TS[type]} => { ${t} ${r.pick(["=", "+=", "-="])} ${value()}; return ${value()} }`,
        r.pick([`${t} ${r.pick(["+=", "-="])} ${b}()`, `${t} = ${t} ${r.pick(["+", "-"])} ${b}()`, `${t} = ${b}() ${r.pick(["+", "-"])} ${t}`, `${t} ${r.pick(["+=", "-="])} (${this.expr("bool", scope, 1)} ? ${b}() : ${value()})`]),
      ]
      scope.names.set(t, { kind: "var", type, mutable: true })
      return lines
    })
    // A variable that holds a value only on some paths.
    add(1.3, () => {
      const type = r.pick(TYPES)
      const [u, k] = [`u${this.counter++}`, `v${this.counter++}`]
      const lines = [`let ${u}: ${TS[type]} | undefined`]
      lines.push(`if (${this.expr("bool", scope, 2)}) ${u} = ${this.expr(type, scope, 2)}`)
      if (r.chance(0.4)) lines.push(`else if (${this.expr("bool", scope, 2)}) ${u} = ${this.expr(type, scope, 2)}`)
      lines.push(r.chance(0.5)
        ? `const ${k}: ${TS[type]} = ${u} === undefined ? ${this.expr(type, scope, 2)} : ${u}`
        : `const ${k}: ${TS[type]} = ${u} !== undefined ? ${u} : ${this.expr(type, scope, 2)}`)
      scope.names.set(k, { kind: "var", type, mutable: false })
      return lines
    })
    // Objects and lists changed in place. Two names may hold one object, a
    // function may change what it is given, and a change may sit behind a
    // condition or an early return: Node decides what each of those does.
    const BOX = type => `{ v: ${TS[type]}; w: ${TS[type]} }`
    const field = () => r.pick(["v", "w"])
    const boxes = scope.visible().filter(e => e.kind === "box")
    const lists = scope.visible().filter(e => e.kind === "list")
    const update = (target, type) => {
      const value = this.expr(type, scope, 2)
      if (type === "big" || type === "num") {
        if (r.chance(0.15)) return `${target}${r.pick(["++", "--"])}`
        return `${target} ${r.pick(type === "num" || context.loop ? ["=", "+=", "-="] : ["=", "+=", "-=", "*="])} ${value}`
      }
      return `${target} ${type === "str" && !context.loop ? r.pick(["=", "+="]) : "="} ${value}`
    }
    add(1.6, () => {
      const type = r.pick(TYPES)
      const name = `b${this.counter++}`
      const same = boxes.filter(b => b.type === type)
      const other = () => {
        const chosen = r.pick(same)
        scope.noteRead(chosen.name)
        return chosen.name
      }
      const roll = r.next()
      const value = same.length && roll < 0.25 ? other()
        : same.length && roll < 0.4 ? `{ ...${other()} }`
        : same.length && roll < 0.5 ? `(${this.expr("bool", scope, 2)} ? ${other()} : ${other()})`
        : `{ v: ${this.expr(type, scope, 2)}, w: ${this.expr(type, scope, 2)} }`
      scope.names.set(name, { kind: "box", type })
      return [`const ${name}: ${BOX(type)} = ${value}`]
    })
    add(1.2, () => {
      const type = r.pick(TYPES)
      const name = `l${this.counter++}`
      const same = lists.filter(l => l.type === type)
      const other = () => {
        const chosen = r.pick(same)
        scope.noteRead(chosen.name)
        return chosen.name
      }
      const roll = r.next()
      const value = same.length && roll < 0.25 ? other()
        : same.length && roll < 0.4 ? `[...${other()}]`
        : `[${Array.from({ length: 1 + r.int(2) }, () => this.expr(type, scope, 2)).join(", ")}]`
      scope.names.set(name, { kind: "list", type })
      return [`const ${name}: ${TS[type]}[] = ${value}`]
    })
    if (boxes.length) {
      const pickBox = type => {
        const chosen = r.pick(type ? boxes.filter(b => b.type === type) : boxes)
        scope.noteRead(chosen.name)
        return chosen
      }
      add(3, () => {
        const box = pickBox()
        return [update(`${box.name}.${field()}`, box.type)]
      })
      // A function that changes the object it is given, perhaps only on some paths.
      add(1.5, () => {
        const box = pickBox()
        const type = box.type
        const [fn, o, k] = [`g${this.counter++}`, `o${this.counter++}`, `v${this.counter++}`]
        const inner = new Scope(scope, true)
        inner.names.set(o, { kind: "box", type })
        const body = []
        if (r.chance(0.5)) body.push(`if (${this.expr("bool", inner, 2)}) return ${this.expr(type, inner, 1)}`)
        body.push(`${o}.${field()} = ${this.expr(type, inner, 2)}`)
        const lines = [`const ${fn} = (${o}: ${BOX(type)}): ${TS[type]} => {`, ...body.map(l => "  " + l), `  return ${o}.${field()}`, "}"]
        const roll = r.next()
        const call = roll < 0.5 ? `${fn}(${box.name})`
          : roll < 0.8 ? `(${this.expr("bool", scope, 2)} ? ${fn}(${box.name}) : ${fn}(${pickBox(type).name}))`
          : `${fn}({ ...${box.name} })`
        lines.push(`const ${k}: ${TS[type]} = ${call}`)
        if (r.chance(0.3)) lines.push(`${fn}(${pickBox(type).name})`)
        scope.names.set(k, { kind: "var", type, mutable: false })
        return lines
      })
      // A function that keeps changing the object it closed over.
      add(0.8, () => {
        const box = pickBox()
        const t = `t${this.counter++}`
        const inner = new Scope(scope, true)
        const lines = [`const ${t} = (): void => {`, `  ${box.name}.${field()} = ${this.expr(box.type, inner, 2)}`, "}", `${t}()`]
        if (r.chance(0.5)) lines.push(r.chance(0.5) ? `${t}()` : `if (${this.expr("bool", scope, 2)}) ${t}()`)
        return lines
      })
      // One loop over two names, which may be two names for one object.
      add(1, () => {
        const box = pickBox()
        const o = `o${this.counter++}`
        const operator = box.type === "big" || box.type === "num" ? r.pick(["=", "+=", "-="]) : "="
        return [`for (const ${o} of [${box.name}, ${pickBox(box.type).name}]) ${o}.${field()} ${operator} ${this.expr(box.type, scope, 1)}`]
      })
      // A change JavaScript may skip, where the model would always make it: this has to be refused.
      add(0.4, () => {
        const box = pickBox()
        const k = `v${this.counter++}`
        const change = `((o: ${BOX(box.type)}): boolean => { o.${field()} = ${this.expr(box.type, new Scope(scope, true), 1)}; return ${r.chance(0.5)} })(${box.name})`
        const line = r.chance(0.6)
          ? `const ${k}: boolean = (${this.expr("bool", scope, 2)} ${r.pick(["&&", "||"])} ${change})`
          : `const ${k}: boolean = [${this.expr("bool", scope, 1)}, ${this.expr("bool", scope, 1)}].${r.pick(["some", "every"])}(e => e && ${change})`
        scope.names.set(k, { kind: "var", type: "bool", mutable: false })
        return [line]
      })
    }
    // Objects that hold other objects. Storing one and then changing it, or
    // changing it through where it is stored, has to be seen from every side.
    const holders = scope.visible().filter(e => e.kind === "holder")
    const queues = scope.visible().filter(e => e.kind === "queue")
    const boxOf = type => {
      const same = boxes.filter(b => b.type === type)
      if (!same.length || r.chance(0.2)) return `{ v: ${this.expr(type, scope, 1)}, w: ${this.expr(type, scope, 1)} }`
      const chosen = r.pick(same)
      scope.noteRead(chosen.name)
      return chosen.name
    }
    const named = entry => {
      scope.noteRead(entry.name)
      return entry
    }
    add(boxes.length ? 1.4 : 0.3, () => {
      const type = boxes.length ? r.pick(boxes).type : r.pick(TYPES)
      const name = `h${this.counter++}`
      const same = holders.filter(h => h.type === type)
      const value = same.length && r.chance(0.2) ? named(r.pick(same)).name : `{ box: ${boxOf(type)} }`
      scope.names.set(name, { kind: "holder", type })
      return [`const ${name}: { box: ${BOX(type)} } = ${value}`]
    })
    add(boxes.length ? 1.2 : 0.2, () => {
      const type = boxes.length ? r.pick(boxes).type : r.pick(TYPES)
      const name = `q${this.counter++}`
      const same = queues.filter(q => q.type === type)
      const value = same.length && r.chance(0.2) ? named(r.pick(same)).name
        : same.length && r.chance(0.15) ? `[...${named(r.pick(same)).name}]`
        : `[${Array.from({ length: 1 + r.int(2) }, () => boxOf(type)).join(", ")}]`
      scope.names.set(name, { kind: "queue", type })
      return [`const ${name}: ${BOX(type)}[] = ${value}`]
    })
    if (holders.length) {
      add(2.2, () => {
        const holder = named(r.pick(holders))
        return [`${holder.name}.box = ${boxOf(holder.type)}`]
      })
      add(1.8, () => {
        const holder = named(r.pick(holders))
        return [update(`${holder.name}.box.${field()}`, holder.type)]
      })
    }
    if (queues.length) {
      add(2, () => {
        const queue = named(r.pick(queues))
        const roll = r.next()
        const position = r.chance(0.5) ? "0" : `${queue.name}.length - 1`
        if (roll < 0.3) return [`${queue.name}.push(${boxOf(queue.type)})`]
        if (roll < 0.55) return [`${queue.name}[${position}] = ${boxOf(queue.type)}`]
        if (roll < 0.85) return [update(`${queue.name}[${position}]!.${field()}`, queue.type)]
        const o = `o${this.counter++}`
        return [`for (const ${o} of ${queue.name}) ${o}.${field()} = ${this.expr(queue.type, scope, 1)}`]
      })
    }
    // An object stored somewhere and changed, both behind one condition that
    // depends on an input. Whatever is read afterwards through the place it
    // was stored has to be the object as that side left it.
    add(1.5, () => {
      const type = r.pick(["big", "num"])
      const [node, keeper] = [`b${this.counter++}`, `${r.chance(0.5) ? "h" : "q"}${this.counter++}`]
      const held = keeper.startsWith("h")
      const place = held ? `${keeper}.box` : `${keeper}[0]`
      const inputs = scope.visible().filter(e => e.kind === "var" && e.domain)
      const condition = () => {
        if (!inputs.length || r.chance(0.2)) return this.expr("bool", scope, 2)
        const input = named(r.pick(inputs))
        return `((${input.name} as ${TS[input.type]}) === (${literal(r.pick(input.domain))} as ${TS[input.type]}))`
      }
      const fresh = () => `{ v: ${literal(this.value(type))}, w: ${literal(this.value(type))} }`
      const steps = () => {
        const store = held || r.chance(0.6) ? `${place} = ${node}` : `${keeper}.push(${node})`
        const change = `${node}.${field()} ${r.pick(["=", "+=", "-="])} ${this.expr(type, scope, 1)}`
        const through = `${place}${held ? "" : "!"}.${field()} ${r.pick(["=", "+="])} ${this.expr(type, scope, 1)}`
        const lines = r.chance(0.5) ? [store, change] : [change, store]
        if (r.chance(0.4)) lines.push(through)
        return lines.map(l => "  " + l)
      }
      const lines = [
        `const ${node}: ${BOX(type)} = ${fresh()}`,
        held ? `const ${keeper}: { box: ${BOX(type)} } = { box: ${fresh()} }` : `const ${keeper}: ${BOX(type)}[] = [${fresh()}]`,
        `if (${condition()}) {`, ...steps(), "}",
      ]
      if (r.chance(0.4)) lines.push("else {", ...steps(), "}")
      scope.names.set(node, { kind: "box", type })
      scope.names.set(keeper, { kind: held ? "holder" : "queue", type })
      // Make the outcome depend on what is read through the place the object was stored.
      const read = held ? `${keeper}.box.${field()}` : `${keeper}[${r.chance(0.5) ? "0" : `${keeper}.length - 1`}]!.${field()}`
      lines.push(`if ((${read} as ${TS[type]}) === (${literal(this.value(type))} as ${TS[type]})) return ${this.expr(context.returns, scope, 1)}`)
      return lines
    })
    if (lists.length) {
      const pickList = () => {
        const chosen = r.pick(lists)
        scope.noteRead(chosen.name)
        return chosen
      }
      add(2, () => {
        const list = pickList()
        const value = this.expr(list.type, scope, 2)
        const roll = r.next()
        if (roll < 0.35) return [`${list.name}.push(${value})`]
        if (roll < 0.5) return [`${list.name}.unshift(${value})`]
        if (roll < 0.65) return [`${list.name}.reverse()`]
        if (roll < 0.8) return [`if (${list.name}.length > 1) ${list.name}.${r.pick(["pop", "shift"])}()`]
        return [`${list.name}[${roll < 0.9 ? "0" : `${list.name}.length - 1`}] = ${value}`]
      })
      // Everything in the list, folded into a value the rest of the function can use.
      add(1, () => {
        const list = pickList()
        const k = `v${this.counter++}`
        if (list.type === "big") {
          scope.names.set(k, { kind: "var", type: "big", mutable: true })
          return r.chance(0.5)
            ? [`let ${k}: bigint = 0n`, `for (const x of ${list.name}) ${k} += x`]
            : [`let ${k}: bigint = 0n`, `${list.name}.forEach(x => { ${k} += x })`]
        }
        scope.names.set(k, { kind: "var", type: "num", mutable: false })
        return [`const ${k}: number = ${list.name}.length`]
      })
    }
    const total = choices.reduce((sum, [weight]) => sum + weight, 0)
    let roll = r.next() * total
    for (const [weight, make] of choices) if ((roll -= weight) < 0) return make()
    return []
  }

  /** A whole program: an exported function over a small finite domain, and what it needs at module level. */
  program(unbounded = false) {
    const r = this.random
    const name = `f${this.index}`
    const count = 1 + r.int(3)
    const params = []
    for (let i = 0; i < count; i++) {
      const type = unbounded && i === 0 ? r.pick(["big", "num"]) : r.pick(TYPES)
      const domain = type === "bool" ? [true, false]
        : r.sample(type === "big" ? BIGS : type === "num" ? NUMS : STRS, type === "str" ? 2 + r.int(2) : 2 + r.int(3))
      const param = { name: `p${i}`, local: `w${i}`, type, domain }
      if (unbounded && type === "big") Object.assign(param, { written: "bigint", input: "bigint", range: [-60n, 60n] })
      // A range too wide to list is stated as bounds; a narrow one is listed, and stated as bounds where that is enough.
      if (unbounded && type === "num") Object.assign(param, r.chance(0.7) ? { written: "number", input: "Integer<-1000, 1000>", range: [-1000, 1000] } : { written: "number", input: "Integer<0, 9>", range: [0, 9] })
      params.push(param)
    }
    const scope = new Scope(undefined, true)
    const header = []
    for (const p of params) {
      // The parameter keeps its literal type for table lookups; a widened copy is what the body computes with.
      scope.names.set(p.name, { kind: "param", type: p.type })
      scope.names.set(p.local, { kind: "var", type: p.type, mutable: false, domain: p.domain })
      header.push(`const ${p.local}: ${TS[p.type]} = ${p.name}`)
    }
    const module = []
    const keyed = params.find(p => p.type === "str")
    if (keyed && r.chance(0.6)) {
      const type = r.pick(TYPES)
      const list = r.chance(0.4)
      const entries = keyed.domain.map(key => `${JSON.stringify(key)}: ${list ? `[${Array.from({ length: r.int(3) }, () => show(this.value(type))).join(", ")}]` : show(this.value(type))}`)
      module.push(`const T${this.index}: Record<${keyed.domain.map(k => JSON.stringify(k)).join(" | ")}, ${list ? `readonly ${TS[type]}[]` : TS[type]}> = { ${entries.join(", ")} }`)
      this.tables.push({ name: `T${this.index}`, key: keyed.name, type, list })
    }
    const returns = r.pick(TYPES)
    const body = this.block(scope, { returns, loop: false }, 2, 2 + r.int(5))
    const signature = params.map(p => `${p.name}: ${p.written ?? p.domain.map(show).join(" | ")}`).join(", ")
    const source = [
      "const call = <T,>(f: () => T): T => f()",
      ...module,
      `export function ${name}(${signature}): ${TS[returns]} {`,
      ...[...header, ...body, `return ${this.expr(returns, scope, 3)}`].map(l => "  " + l),
      "}",
      "",
    ].join("\n")
    return { name, params, returns, source }
  }
}

/** Copies of the function under another name, each with one constant or operator changed. */
function mutate(program, random) {
  const start = program.source.indexOf("export function")
  const body = program.source.slice(start)
  // Only swaps that keep the types right: `-` and `*` are never strings, and the equality swaps sit between two casts.
  const swaps = [[" - ", " + "], [" * ", " + "], [" * ", " - "], [" < ", " <= "], [" <= ", " < "], [" > ", " >= "], [" >= ", " > "], [") === (", ") !== ("], [") !== (", ") === ("], [" && ", " || "], [" || ", " && "]]
  const sites = []
  for (const [from, to] of swaps) for (let at = body.indexOf(from); at >= 0; at = body.indexOf(from, at + 1)) sites.push({ at, length: from.length, text: to })
  for (const match of body.matchAll(/\((\(?-?\d+n?\)?) as (bigint|number)\)/g)) {
    const digits = /-?\d+/.exec(match[1])[0]
    const changed = match[1].includes("n") ? `(${BigInt(digits) + 1n}n)` : `(${Number(digits) + 1})`
    sites.push({ at: match.index, length: match[0].length, text: `(${changed} as ${match[2]})` })
  }
  for (const match of body.matchAll(/\((true|false) as boolean\)/g)) sites.push({ at: match.index, length: match[0].length, text: `(${match[1] === "true" ? "false" : "true"} as boolean)` })
  // The header copies parameters into locals; leave it and the signature alone.
  const from = body.indexOf("{")
  const usable = sites.filter(site => site.at > from)
  const mutant = `m${program.name.slice(1)}`
  return random.sample(usable, 8).map(site => ({
    name: mutant,
    source: (body.slice(0, site.at) + site.text + body.slice(site.at + site.length)).replace(`export function ${program.name}(`, `export function ${mutant}(`),
  }))
}

/** Inputs to compare a function with its mutant on, when its inputs cannot all be listed. */
function sampleInputs(params, random, count) {
  const one = p => {
    if (!p.range) return random.pick(p.domain)
    const [low, high] = p.range
    const span = Number(high) - Number(low) + 1
    const value = random.chance(0.3) ? Number(random.pick(p.type === "big" ? BIGS : NUMS)) : Number(low) + random.int(span)
    const inside = Math.min(Number(high), Math.max(Number(low), value))
    return p.type === "big" ? BigInt(inside) : inside
  }
  return Array.from({ length: count }, () => params.map(one))
}

// ------------------------------------------------------------------ oracle

function inputsOf(params) {
  return params.reduce((rows, p) => rows.flatMap(row => p.domain.map(value => [...row, value])), [[]])
}

/** What Node computes for each input: a value, or the fact that it threw or left the exact numbers. */
function truthOf(fn, params) {
  return inputsOf(params).map(input => {
    try {
      const value = fn(...input)
      if (typeof value === "number" && !Number.isSafeInteger(value)) return { input, fails: "inexact" }
      return { input, value: Object.is(value, -0) ? 0 : value }
    } catch (error) {
      return { input, fails: error instanceof Error ? error.constructor.name : "throw" }
    }
  })
}

function lawSource(program, truth, wrongAt) {
  const names = program.params.map((_, i) => `a${i}`)
  const type = TS[program.returns]
  const expected = (entry, index) => {
    if (entry.fails) return literal(program.returns === "bool" ? false : program.returns === "big" ? 0n : program.returns === "num" ? 0 : "")
    const value = index === wrongAt
      ? typeof entry.value === "boolean" ? !entry.value : typeof entry.value === "bigint" ? entry.value + 1n : typeof entry.value === "number" ? entry.value + 1 : entry.value + "!"
      : entry.value
    return literal(value)
  }
  const when = entry => entry.input.map((value, i) => `(${names[i]} as ${TS[program.params[i].type]}) === ${literal(value)}`).join(" && ")
  const chain = truth.slice(0, -1).map((entry, i) => `${when(entry)} ? (${expected(entry, i)} as ${type})`).join("\n      : ")
  const last = `(${expected(truth.at(-1), truth.length - 1)} as ${type})`
  const table = truth.length > 1 ? `${chain}\n      : ${last}` : last
  const domain = program.params.map(p => p.domain.map(show).join(" | ")).join(", ")
  return `law("${wrongAt === undefined ? "A" : "B"} ${program.name}", domain<[${domain}]>(), ([${names.join(", ")}]) => {
  expect<${type}>(${program.name}(${names.join(", ")})).toEqual(
    ${table},
  )
})\n`
}

// -------------------------------------------------------------------- run

const seed = Number(options.seed)
const total = Number(options.programs)
const batchSize = Number(options.batch)
const lean = process.env.PUDDING_LEAN ?? locateLean({}, root)
const workRoot = join(root, ".lab", "fuzz")
const failures = join(workRoot, "failures")
const tally = { programs: 0, proved: 0, unsupported: 0, throwing: 0, equivalent: 0, typeErrors: 0, disagreements: 0, wrongProofs: 0 }
const problems = []
const reasons = new Map()

async function runUnboundedBatch(batch, first) {
  const directory = join(workRoot, `seed-${seed}-unbounded-${batch}`)
  rmSync(directory, { recursive: true, force: true })
  mkdirSync(directory, { recursive: true })
  const cases = []
  for (let i = 0; i < batchSize && first + i < total; i++) {
    const index = first + i
    const random = new Random(seed * 1_000_003 + index)
    const program = new Generator(random, index).program(true)
    const run = (fn, input) => {
      try {
        const value = fn(...input)
        return typeof value === "number" && !Number.isSafeInteger(value) ? { fails: true } : { value: Object.is(value, -0) ? 0 : value }
      } catch {
        return { fails: true }
      }
    }
    // Try several mutants and keep the first one Node can tell from the original:
    // the law that the two are equal is certainly false where both return different things.
    const inputs = sampleInputs(program.params, random, 400)
    let mutant
    let differs
    for (const [k, candidate] of mutate(program, random).entries()) {
      const trial = join(directory, `trial-${index}-${k}.ts`)
      writeFileSync(trial, program.source + "\n" + candidate.source)
      try {
        const module = await import(pathToFileURL(trial).href)
        const original = inputs.map(input => run(module[program.name], input))
        const at = inputs.findIndex((input, n) => {
          const other = run(module[candidate.name], input)
          return !original[n].fails && !other.fails && original[n].value !== other.value
        })
        mutant ??= candidate
        if (at >= 0) {
          mutant = candidate
          differs = inputs[at]
        }
      } catch {
        // A mutant Node cannot load is no use; try the next.
      } finally {
        rmSync(trial, { force: true })
      }
      if (differs) break
    }
    if (!mutant) {
      tally.typeErrors++
      continue
    }
    writeFileSync(join(directory, `${program.name}.ts`), program.source + "\n" + mutant.source)
    const names = program.params.map((_, n) => `a${n}`)
    const domain = program.params.map(p => p.input ?? p.domain.map(show).join(" | ")).join(", ")
    writeFileSync(join(directory, `${program.name}.law.ts`), `import { domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { ${program.name}, ${mutant.name} } from "./${program.name}.ts"

law("M ${program.name}", domain<[${domain}]>(), ([${names.join(", ")}]) => {
  expect<${TS[program.returns]}>(${program.name}(${names.join(", ")})).toEqual(${mutant.name}(${names.join(", ")}))
})
`)
    cases.push({ program, differs })
  }
  const report = runPudding(directory, cases)
  for (const { program, differs } of cases) {
    tally.programs++
    const entry = report.laws.find(law => law.name === `M ${program.name}`)
    if (!differs) {
      tally.equivalent++
      continue
    }
    tally.throwing++
    if (!entry || entry.status === "proved") {
      problems.push({ kind: "wrong proof", program: program.name, detail: `the function and its mutant differ at (${differs.map(show).join(", ")}) but the law that they are equal was reported ${entry?.status ?? "missing"}` })
      tally.wrongProofs++
      const kept = join(failures, `seed-${seed}-unbounded-${program.name}`)
      mkdirSync(kept, { recursive: true })
      for (const file of [`${program.name}.ts`, `${program.name}.law.ts`]) cpSync(join(directory, file), join(kept, file))
    } else if (entry.findings.some(f => f.kind === "counterexample")) tally.proved++
    else tally.unsupported++
  }
  if (!options.keep && !problems.some(p => cases.some(c => c.program.name === p.program))) rmSync(directory, { recursive: true, force: true })
}

/** Run Pudding on a batch, dropping programs TypeScript rejects, and return its report. */
function runPudding(directory, cases) {
  let report
  for (let attempt = 0; attempt < 3; attempt++) {
    const args = [process.env.PUDDING_CLI ?? join(root, "dist", "cli.js"), "--cwd", directory, "--no-cache", "--reporter", "json", ...(options["cross-check"] ? [] : ["--no-cross-check"])]
    const result = spawnSync("node", args, { encoding: "utf8", env: { ...process.env, PUDDING_LEAN: lean }, maxBuffer: 1 << 28 })
    try {
      report = JSON.parse(result.stdout)
    } catch {
      throw new Error(`Pudding did not produce a report for ${directory}:\n${result.stdout.slice(0, 2000)}\n${result.stderr.slice(0, 2000)}`)
    }
    // A program TypeScript rejects is a generator slip. Drop it and try the rest again.
    const rejected = new Set(report.errors.flatMap(error => [...error.matchAll(/\b(f\d+)\.(?:law\.)?ts/g)].map(match => match[1])))
    if (!report.errors.length) break
    if (!rejected.size) throw new Error(`Pudding reported errors that name no program:\n${report.errors.join("\n")}`)
    for (const name of rejected) {
      if (!options.quiet) {
        const where = /\b(f\d+\.(?:law\.)?ts):(\d+):/.exec(report.errors.find(e => e.includes(name + ".")) ?? "")
        console.log(`  ${name}: rejected by TypeScript (${report.errors.find(e => e.includes(name + "."))?.slice(0, 160)})`)
        if (where) console.log(`    ${readFileSync(join(directory, where[1]), "utf8").split("\n")[Number(where[2]) - 1]?.trim().slice(0, 200)}`)
      }
      rmSync(join(directory, `${name}.ts`), { force: true })
      rmSync(join(directory, `${name}.law.ts`), { force: true })
      const at = cases.findIndex(c => c.program.name === name)
      if (at >= 0) {
        cases.splice(at, 1)
        tally.typeErrors++
      }
    }
  }
  if (report.errors.length) throw new Error(`Pudding still reports errors for ${directory}:\n${report.errors.join("\n")}`)
  return report
}

async function runBatch(batch, first) {
  const directory = join(workRoot, `seed-${seed}-batch-${batch}`)
  rmSync(directory, { recursive: true, force: true })
  mkdirSync(directory, { recursive: true })
  const cases = []
  for (let i = 0; i < batchSize && first + i < total; i++) {
    const index = first + i
    const program = new Generator(new Random(seed * 1_000_003 + index), index).program()
    writeFileSync(join(directory, `${program.name}.ts`), program.source)
    let truth
    try {
      const module = await import(pathToFileURL(join(directory, `${program.name}.ts`)).href)
      truth = truthOf(module[program.name], program.params)
    } catch (error) {
      // The generator produced something Node cannot even load; that is a generator bug, not a finding.
      tally.typeErrors++
      rmSync(join(directory, `${program.name}.ts`))
      if (!options.quiet) console.log(`  ${program.name}: not loadable (${String(error).split("\n")[0]})`)
      continue
    }
    const sound = truth.findIndex(entry => !entry.fails)
    const laws = [lawSource(program, truth, undefined), ...(sound >= 0 ? [lawSource(program, truth, sound)] : [])]
    writeFileSync(join(directory, `${program.name}.law.ts`), `import { domain, expect, law } from "@bytewaveco/pudding"\nimport { ${program.name} } from "./${program.name}.ts"\n\n${laws.join("\n")}`)
    cases.push({ program, truth, throws: truth.some(entry => entry.fails) })
  }
  const report = runPudding(directory, cases)
  for (const { program, truth, throws } of cases) {
    tally.programs++
    const entry = kind => report.laws.find(law => law.name === `${kind} ${program.name}`)
    const a = entry("A")
    const b = entry("B")
    // Refused: the code is outside the subset, or a number stopped being a whole
    // number on some input (NaN, say), where the model does not describe the program at all.
    // With the cross-check on, refused code is executed instead and comes back as checked.
    const refused = law => law.status === "checked" || law.status === "sampled" || (law.status === "failed" && law.findings.length > 0 &&
      (law.findings.every(f => f.kind === "unsupported") || law.findings.some(f => f.kind === "inexact")))
    const record = (kind, detail) => {
      problems.push({ kind, program: program.name, detail })
      if (kind === "wrong proof") tally.wrongProofs++
      else tally.disagreements++
      const kept = join(failures, `seed-${seed}-${program.name}`)
      mkdirSync(kept, { recursive: true })
      for (const file of [`${program.name}.ts`, `${program.name}.law.ts`]) cpSync(join(directory, file), join(kept, file))
      writeFileSync(join(kept, "verdict.json"), JSON.stringify({ kind, detail, truth, a, b }, (_, v) => (typeof v === "bigint" ? `${v}n` : v), 2))
    }
    if (!a || (truth.some(e => !e.fails) && !b)) {
      record("disagreement", "a law is missing from the report")
      continue
    }
    if (b && b.status !== "failed") record("wrong proof", `law B is false but was reported ${b.status}`)
    if (throws) {
      tally.throwing++
      if (a.status !== "failed") record("wrong proof", `some input fails in Node (${truth.find(e => e.fails).fails}) but law A was reported ${a.status}`)
    } else if (a.status === "proved") tally.proved++
    else if (refused(a)) {
      tally.unsupported++
      // Why it was refused, with names and positions taken out so that like reasons count together.
      const why = (a.findings.find(f => f.kind === "unsupported" || f.kind === "inexact")?.message ?? a.notes[0] ?? a.status)
        .replace(/`[^`]*`/g, "`…`").replace(/\(?[\w./-]+\.ts:\d+(:\d+)?\)?/g, "").replace(/ at line \d+/g, "").replace(/;.*$/, "").trim()
      reasons.set(why, (reasons.get(why) ?? 0) + 1)
    }
    else record("disagreement", `law A is true but was reported ${a.status}: ${a.findings.map(f => `${f.kind}: ${f.message}`).join("; ").slice(0, 300)}`)
  }
  if (!options.keep && !problems.some(p => cases.some(c => c.program.name === p.program))) rmSync(directory, { recursive: true, force: true })
}

const started = performance.now()
for (let batch = 0, first = 0; first < total; batch++, first += batchSize) {
  await (options.unbounded ? runUnboundedBatch(batch, first) : runBatch(batch, first))
  if (!options.quiet) console.log(`batch ${batch}: ${JSON.stringify(tally)}`)
}
console.log(`\nseed ${seed}: ${tally.programs} programs in ${((performance.now() - started) / 1000).toFixed(1)} s`)
if (options.unbounded) {
  console.log(`  mutants Node tells apart      ${tally.throwing}`)
  console.log(`    refuted with an input       ${tally.proved}`)
  console.log(`    not proved, or refused      ${tally.unsupported}`)
  console.log(`  mutants Node cannot tell apart ${tally.equivalent}`)
} else {
  console.log(`  proved as expected      ${tally.proved}`)
  console.log(`  refused as unsupported  ${tally.unsupported}`)
  console.log(`  throw for some input    ${tally.throwing}`)
}
console.log(`  generator slips         ${tally.typeErrors}`)
console.log(`  disagreements           ${tally.disagreements}`)
console.log(`  WRONG PROOFS            ${tally.wrongProofs}`)
for (const [why, count] of [...reasons].sort((x, y) => y[1] - x[1])) console.log(`    ${String(count).padStart(4)}  ${why.slice(0, 150)}`)
for (const problem of problems) console.log(`  ${problem.kind}: ${problem.program}: ${problem.detail}`)
if (problems.length) console.log(`\nkept under ${failures}`)
process.exitCode = tally.wrongProofs || tally.disagreements ? 1 : 0
