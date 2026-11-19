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
//   node scripts/fuzz.mjs [--seed N] [--programs N] [--batch N] [--cross-check]
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
    "cross-check": { type: "boolean", default: false }, quiet: { type: "boolean", default: false },
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
      const candidates = scope.visible().filter(e => e.kind === "var" && e.type === type && !(e.outside && e.mutable))
      if (candidates.length && r.chance(0.75)) {
        const chosen = r.pick(candidates)
        scope.noteRead(chosen.name)
        return chosen.name
      }
      return `(${literal(this.value(type))} as ${TS[type]})`
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
    const table = this.tables.find(t => !t.list && t.type === type && scope.lookup(t.key))
    if (table) add(1.5, () => `${table.name}[${table.key}]`)
    const listTable = this.tables.find(t => t.list && scope.lookup(t.key))
    if (listTable && type === "bool") add(1.5, () => `${listTable.name}[${listTable.key}].includes(${sub(listTable.type)})`)
    if (type === "bool") {
      const cmp = r.pick(["big", "num"])
      add(2, () => `(!${sub("bool")})`)
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
      add(1, () => `[${sub("big")}, ${sub("big")}, ${sub("big")}].reduce((s, e) => s ${r.pick(["+", "-", "*"])} e, ${sub("big")})`)
    } else if (type === "num") {
      add(4, () => `(${sub("num")} ${r.pick(["+", "-", "*"])} ${sub("num")})`)
      add(1, () => `(-${sub("num")})`)
      add(1.5, () => `(${sub("num")} % ${literal(r.pick(NUMS.filter(v => v !== 0)))})`)
      add(0.3, () => `(${sub("num")} % ${sub("num")})`)
      add(2, () => `Math.${r.pick(["floor", "trunc", "ceil"])}(${sub("num")} / ${literal(r.pick(NUMS.filter(v => v !== 0)))})`)
      add(1.5, () => `Math.${r.pick(["abs", "sign"])}(${sub("num")})`)
      add(1.5, () => `Math.${r.pick(["min", "max"])}(${sub("num")}, ${sub("num")})`)
      add(0.7, () => `Number(${sub("big")})`)
      add(0.7, () => `[${sub(r.pick(TYPES))}, ${sub("bool")}].length`)
      if (listTable) add(1, () => `${listTable.name}[${listTable.key}].length`)
    } else {
      add(3, () => `(${sub("str")} + ${sub("str")})`)
      add(3, () => {
        const t = r.pick(["str", "big", "num"])
        return `\`${r.pick(["", "<", "n="])}\${${sub(t)}}${r.pick(["", ">", ":"])}\${${sub("str")}}\``
      })
      add(1, () => `String(${sub(r.pick(["big", "num"]))})`)
      add(1, () => `(${sub(r.pick(["big", "num"]))}).toString()`)
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
    const assignable = scope.visible().filter(e => e.kind === "var" && e.mutable && !e.outside)
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
        const name = this.fresh(inner, type, "x")
        inner.names.set(name, { kind: "var", type })
        const body = this.block(inner, { ...context, loop: true }, depth - 1, 1 + r.int(3))
        return [`for (const ${name} of [${items.join(", ")}]) {`, ...body.map(l => "  " + l), "}"]
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
        for (const label of labels) {
          lines.push(`  case ${show(label)}: {`, ...nested({ loop: false }).map(l => "  " + l), "  }")
          if (r.chance(0.7)) lines.push("  break")
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
    const total = choices.reduce((sum, [weight]) => sum + weight, 0)
    let roll = r.next() * total
    for (const [weight, make] of choices) if ((roll -= weight) < 0) return make()
    return []
  }

  /** A whole program: an exported function over a small finite domain, and what it needs at module level. */
  program() {
    const r = this.random
    const name = `f${this.index}`
    const count = 1 + r.int(3)
    const params = []
    for (let i = 0; i < count; i++) {
      const type = r.pick(TYPES)
      const domain = type === "bool" ? [true, false]
        : r.sample(type === "big" ? BIGS : type === "num" ? NUMS : STRS, type === "str" ? 2 + r.int(2) : 2 + r.int(3))
      params.push({ name: `p${i}`, local: `w${i}`, type, domain })
    }
    const scope = new Scope(undefined, true)
    const header = []
    for (const p of params) {
      // The parameter keeps its literal type for table lookups; a widened copy is what the body computes with.
      scope.names.set(p.name, { kind: "param", type: p.type })
      scope.names.set(p.local, { kind: "var", type: p.type, mutable: false })
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
    const signature = params.map(p => `${p.name}: ${p.domain.map(show).join(" | ")}`).join(", ")
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
const tally = { programs: 0, proved: 0, unsupported: 0, throwing: 0, typeErrors: 0, disagreements: 0, wrongProofs: 0 }
const problems = []

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
    writeFileSync(join(directory, `${program.name}.law.ts`), `import { domain, expect, law } from "pudding"\nimport { ${program.name} } from "./${program.name}.ts"\n\n${laws.join("\n")}`)
    cases.push({ program, truth, throws: truth.some(entry => entry.fails) })
  }
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
        if (where) console.log(`    ${readFileSync(join(directory, where[1]), "utf8").split("\n")[Number(where[2]) - 1]?.trim().slice(0, 200)}`)
      }
      rmSync(join(directory, `${name}.ts`), { force: true })
      rmSync(join(directory, `${name}.law.ts`), { force: true })
      const at = cases.findIndex(c => c.program.name === name)
      if (at >= 0) {
        cases.splice(at, 1)
        tally.typeErrors++
        if (!options.quiet) console.log(`  ${name}: rejected by TypeScript (${report.errors.find(e => e.includes(name + "."))?.slice(0, 160)})`)
      }
    }
  }
  if (report.errors.length) throw new Error(`Pudding still reports errors for ${directory}:\n${report.errors.join("\n")}`)
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
    else if (refused(a)) tally.unsupported++
    else record("disagreement", `law A is true but was reported ${a.status}: ${a.findings.map(f => `${f.kind}: ${f.message}`).join("; ").slice(0, 300)}`)
  }
  if (!problems.some(p => cases.some(c => c.program.name === p.program))) rmSync(directory, { recursive: true, force: true })
}

const started = performance.now()
for (let batch = 0, first = 0; first < total; batch++, first += batchSize) {
  await runBatch(batch, first)
  if (!options.quiet) console.log(`batch ${batch}: ${JSON.stringify(tally)}`)
}
console.log(`\nseed ${seed}: ${tally.programs} programs in ${((performance.now() - started) / 1000).toFixed(1)} s`)
console.log(`  proved as expected      ${tally.proved}`)
console.log(`  refused as unsupported  ${tally.unsupported}`)
console.log(`  throw for some input    ${tally.throwing}`)
console.log(`  generator slips         ${tally.typeErrors}`)
console.log(`  disagreements           ${tally.disagreements}`)
console.log(`  WRONG PROOFS            ${tally.wrongProofs}`)
for (const problem of problems) console.log(`  ${problem.kind}: ${problem.program}: ${problem.detail}`)
if (problems.length) console.log(`\nkept under ${failures}`)
process.exitCode = tally.wrongProofs || tally.disagreements ? 1 : 0
