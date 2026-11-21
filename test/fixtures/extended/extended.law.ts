import { describe, domain, expect, law, type Integer } from "@bytewaveco/pudding"
import {
  alwaysThrows, daysOrDefault, FROZEN_DAYS, hasField, listOps, mapDeleteOrder, mapSymbolicDelete, mergeConfig, minOfList, nullAccess, nullOrDefault,
  optionalNull, orderedKeys, paramDefault, requirePositive, roundTripEntries, safeDivide, stackOps,
  stringHelpers, sumVariadic, tagOf,
} from "./extended.ts"

describe("null and mixed unions", () => {
  law("?? replaces null and undefined, while default params only replace undefined", domain<{ v: bigint | null | undefined; fb: bigint }>(), ({ v, fb }) => {
    expect(nullOrDefault(v === undefined ? null : v, fb)).toBe(v === null || v === undefined ? fb : v)
    expect(paramDefault(v)).toBe(v === undefined ? 10n : v)
    expect(v === null).toBe(v === null && v !== undefined)
  })

  law("FALSE: default parameter replaces null", domain<bigint | null>(), v => {
    expect(paramDefault(v)).not.toBeNull()
  })

  law("?. short-circuits on null as well as undefined", domain<{ v: bigint; depth: 0 | 1 | 2 }>(), ({ v, depth }) => {
    const box = depth === 0 ? null : depth === 1 ? { inner: null } : { inner: { v } }
    expect(optionalNull(box)).toBe(depth === 2 ? v : undefined)
  })

  law("FALSE: accessing a property of null throws", domain<{ v: bigint } | null>(), box => {
    expect(nullAccess(box)).toBe(box ? box.v : 0n)
  })

  law("typeof, Array.isArray, Boolean and Number helpers work across mixed unions", domain<bigint | string | boolean | null | undefined>(), x => {
    expect(tagOf(x)).toBe(x === null ? "null" : typeof x)
    expect(Array.isArray(x)).toBe(false)
    expect(Array.isArray([x])).toBe(true)
    expect(Boolean(x)).toBe(!!x)
    expect(Number.isSafeInteger(Number.MAX_SAFE_INTEGER)).toBe(true)
    expect(Number.isNaN(Number.MIN_SAFE_INTEGER)).toBe(false)
    expect(Number.isFinite(Infinity)).toBe(false)
  })
})

describe("in, Object.*, rest and spread", () => {
  law("in and Object.hasOwn distinguish own properties", domain<{ a: bigint; b?: bigint; k: "a" | "b" | "c" }>(), ({ k, ...obj }) => {
    expect(hasField(obj, k)).toBe(Object.hasOwn(obj, k))
    expect(hasField(obj, "a")).toBe(true)
    expect(hasField(obj, "c")).toBe(false)
  })

  law("Object.keys follows JS array-index ordering and Object.fromEntries round-trips", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(orderedKeys(a, b)).toEqual(["0", "2", "z", "a"])
    expect(roundTripEntries(a, b)).toEqual({ a, b })
  })

  law("rest parameters and spread call arguments forward values", domain<[Integer<0, 100>, Integer<0, 100>, Integer<0, 100>]>(), ([a, b, c]) => {
    expect(sumVariadic(BigInt(a), BigInt(b), BigInt(c))).toBe(BigInt(a + b + c))
    expect(minOfList([a, b, c])).toBe(Math.min(a, Math.min(b, c)))
  })
})

describe("array, Map/Set and string methods", () => {
  law("concat, toReversed, indexOf, findIndex, findLast, join, flat, reduceRight and forEach match JS", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    const r = listOps(a, b, c)
    expect(r.rev).toEqual([c, b, a])
    expect(r.idx).toBe(a === b ? 0 : 1)
    expect(r.lastIdx).toBe(c === b ? 2 : 1)
    expect(r.foundIdx).toBe(a > 0n ? 0 : b > 0n ? 1 : c > 0n ? 2 : -1)
    expect(r.foundLast).toBe(c > 0n ? c : b > 0n ? b : a > 0n ? a : undefined)
    expect(r.foundLastIdx).toBe(c > 0n ? 2 : b > 0n ? 1 : a > 0n ? 0 : -1)
    expect(r.joined).toBe(`${a}:::${b}`)
    expect(r.flattened).toEqual([a, b, c])
    expect(r.rightOrder).toBe(`${c}${b}${a}`)
    expect(r.total).toBe(a + b + c)
  })

  law("unshift, pop and shift mutate local arrays in order", domain<[bigint, bigint]>(), ([a, b]) => {
    const r = stackOps(a, b)
    expect(r.top).toBe(a)
    expect(r.head).toBe(b)
    expect(r.remaining).toBe(0)
  })

  law("Map.delete updates size, presence and re-insertion order", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    const r = mapDeleteOrder(a, b, c)
    expect(r.removed).toBe(true)
    expect(r.missing).toBe(false)
    expect(r.keys).toEqual(["y", "x"])
    expect(r.values).toEqual([b, c])
    expect(r.size).toBe(2)
    expect(r.x).toBe(c)
    const sym = mapSymbolicDelete(a, b, c)
    expect(sym.existed).toBe(a === b)
    expect(sym.hasK1).toBe(a !== b)
    expect(sym.size).toBe(a === b ? 0 : 1)
  })

  law("string methods work on finite strings and static symbolic affixes", domain<{ name: "ada" | "grace"; raw: string }>(), ({ name, raw }) => {
    const r = stringHelpers(name, raw)
    expect(r.initial).toBe(name === "ada" ? "A" : "G")
    expect(r.parts).toEqual([name, "ok"])
    expect(r.replaced).toBe(name === "ada" ? "Ada" : "grAce")
    expect(r.replacedAll).toBe(name === "ada" ? "AdA" : "grAce")
    expect(r.prefixed).toBe(true)
    expect(r.suffixed).toBe(true)
    expect(r.includesMid).toBe(true)
  })
})

describe("matchers and range quantification", () => {
  law("extended Vitest matchers and toThrow work as expected", domain<bigint>(), x => {
    if (x > 0n) {
      expect(x + 1n).toBeGreaterThan(x)
      expect(x).toBeGreaterThanOrEqual(1n)
      expect(x - 1n).toBeLessThan(x)
      expect(x).toBeLessThanOrEqual(x)
      expect(x).toBeDefined()
      expect(x).toBeTruthy()
      expect([x, x + 1n]).toHaveLength(2)
      expect([x, x + 1n]).toContain(x)
      expect(() => requirePositive(x)).not.toThrow()
    } else {
      expect(() => requirePositive(x)).toThrow()
      expect(null).toBeNull()
      expect(undefined).toBeUndefined()
      expect(0n).toBeFalsy()
    }
  })

  law("FALSE: toThrow fails when the callback can return normally", domain<bigint>(), x => {
    expect(() => requirePositive(x)).toThrow()
  })

  law("large consecutive finite ranges quantify cleanly", domain<[Integer<1, 200>, Integer<1, 200>]>(), ([a, b]) => {
    expect(a + b).toBeGreaterThanOrEqual(2)
    expect(a + b).toBeLessThanOrEqual(400)
  })
})

describe("soundness regressions from review", () => {
  law("CHECKED: Object.keys on multi-property input record is refused", domain<{ a: 1; b: 2 }>(), x => {
    expect(Object.keys(x)).toEqual(["a", "b"])
  })

  law("Object.keys preserves distinct property order across branches", domain<boolean>(), b => {
    const o = b ? { a: 1, b: 2 } : { b: 2, a: 1 }
    expect(Object.keys(o)).toEqual(b ? ["a", "b"] : ["b", "a"])
  })

  law("FALSE: Object.keys ignores branch property order", domain<boolean>(), b => {
    const o = b ? { a: 1, b: 2 } : { b: 2, a: 1 }
    expect(Object.keys(o)).toEqual(["a", "b"])
  })

  law("shared pop and shift across symbolic branches update array length", domain<boolean>(), b => {
    const a = [1, 2]
    if (b) a.pop()
    else a.pop()
    expect(a).toEqual([1])
    const c = [1, 2]
    if (b) c.shift()
    else c.shift()
    expect(c).toEqual([2])
  })

  law("FALSE: shared pop across symbolic branches leaves length unchanged", domain<boolean>(), b => {
    const a = [1, 2]
    if (b) a.pop()
    else a.pop()
    expect(a.length).toBe(2)
  })

  law("Map and Set iterators observe mutations, exhaust on consumption, and are not arrays", () => {
    const m = new Map([["a", 1]])
    const it = m.keys()
    expect(Array.isArray(it)).toBe(false)
    m.clear()
    expect([...it]).toEqual([])
    const m2 = new Map([["a", 1]])
    const it2 = m2.keys()
    expect([...it2]).toEqual(["a"])
    expect([...it2]).toEqual([])
  })

  law("FALSE: Map.keys returns an eager snapshot", () => {
    const m = new Map([["a", 1]])
    const it = m.keys()
    m.clear()
    expect([...it]).toEqual(["a"])
  })

  law("FALSE: Array.isArray on Map.keys is true", () => {
    const m = new Map([["a", 1]])
    expect(Array.isArray(m.keys())).toBe(true)
  })

  law("forEach skips positions deleted by an earlier callback", () => {
    const a = [1, 2]
    let count = 0
    a.forEach(() => { count++; a.pop() })
    expect(count).toBe(1)
    expect(a).toEqual([1])
  })

  law("FALSE: forEach visits deleted positions", () => {
    const a = [1, 2]
    let count = 0
    a.forEach(() => { count++; a.pop() })
    expect(count).toBe(2)
  })

  law("CHECKED: rest parameter in array callback is refused", () => {
    let count = 0
    ;[1].forEach((...args) => { count = args.length })
    expect(count).toBe(3)
  })

  law("optional arguments in lastIndexOf, join and split match JavaScript", domain<boolean>(), b => {
    expect([1, 2, 2].lastIndexOf(2, undefined)).toBe(-1)
    expect([1, 2, 2].lastIndexOf(2)).toBe(2)
    const sep = b ? undefined : ":"
    expect([1, 2].join(sep)).toBe(b ? "1,2" : "1:2")
    expect("abc".split(undefined as unknown as string, 0)).toEqual([])
  })

  law("FALSE: lastIndexOf with explicit undefined searches from end", () => {
    expect([1, 2, 2].lastIndexOf(2, undefined)).toBe(2)
  })

  law("FALSE: split with undefined separator ignores limit 0", () => {
    expect("abc".split(undefined as unknown as string, 0)).toEqual(["abc"])
  })

  law("Object.hasOwn observes own properties on strings", () => {
    expect(Object.hasOwn("abc" as unknown as object, "length")).toBe(true)
    expect(Object.hasOwn("abc" as unknown as object, "0")).toBe(true)
    expect(Object.hasOwn("abc" as unknown as object, "3")).toBe(false)
  })

  law("FALSE: Object.hasOwn on string ignores length", () => {
    expect(Object.hasOwn("abc" as unknown as object, "length")).toBe(false)
  })

  law("CHECKED: toThrow refuses callbacks containing inner expect", () => {
    expect(() => {
      expect(1).toBe(2)
    }).toThrow()
  })

  law("Boolean, String and Number conversions handle spread arguments", () => {
    const empty: [] = []
    const one: [bigint] = [42n]
    expect(Boolean(...empty)).toBe(false)
    expect(String(...empty)).toBe("")
    expect(Number(...empty)).toBe(0)
    expect(String(...one)).toBe("42")
    expect(Number(...one)).toBe(42)
  })

  law("CHECKED: Object.keys on single-property input record is refused", domain<{ a: 1 }>(), x => {
    expect(Object.keys(x)).toEqual(["a"])
  })

  law("CHECKED: reentrant iterator consumption inside Array.from is refused", () => {
    const m = new Map([["a", 1], ["b", 2], ["c", 3]])
    const it = m.keys()
    expect(Array.from(it, () => [...it].length)).toEqual([2])
  })

  law("CHECKED: reentrant iterator consumption inside for-of is refused", () => {
    const m = new Map([["a", 1], ["b", 2]])
    const it = m.keys()
    const seen: number[] = []
    for (const _k of it) seen.push([...it].length)
    expect(seen).toEqual([1])
  })

  law("CHECKED: side effect in computed key of null element access inside toThrow is refused", () => {
    let calls = 0
    const key = () => { calls++; return "x" }
    expect(() => (null as unknown as Record<string, number>)[key()]).toThrow()
    expect(calls).toBe(1)
  })

  law("CHECKED: side effect in throw operand inside toThrow is refused", () => {
    let calls = 0
    const bump = () => { calls++; return new Error("boom") }
    expect(() => { throw bump() }).toThrow()
    expect(calls).toBe(1)
  })

  law("toThrow guards conditional callbacks, length is in arrays, numeric literals widen in matchers, and clear discards prior history", domain<0 | 1>(), x => {
    expect(x).toBeLessThan(2)
    expect("length" in []).toBe(true)
    const b = x === 1
    const fn = b ? () => { throw new Error("a") } : () => { throw new Error("b") }
    expect(fn).toThrow()
    const m = new Map<string, number>()
    if (b) m.set("x", 1)
    else m.clear()
    m.clear()
    expect(m.size).toBe(0)
  })

  law("symbolic array indexing, Object.freeze, with, toSpliced, 1-arg reduce, flat(Infinity), Math.min/max with Infinity, Map/Set forEach, codePointAt and exponentiation", domain<{ i: Integer<0, 500>; a: bigint; b: bigint; k: "x" | "y" | undefined; pad: "0" | "_" }>(), ({ i, a, b, k, pad }) => {
    expect(daysOrDefault(i)).toBe(i === 0 ? 31 : i === 1 ? 28 : i === 2 ? 31 : i === 3 ? 30 : 0)
    if (i < 4) expect(FROZEN_DAYS[i]!).toBeGreaterThanOrEqual(28)
    expect([a, b].with(-1, 0n)).toEqual([a, 0n])
    expect(() => [a].with(2, 0n)).toThrow()
    expect(([a, b, 0n] as bigint[]).toSpliced(0, 0)).toEqual([a, b, 0n])
    expect([a, b, 0n].toSpliced(1)).toEqual([a])
    expect([a, b, 0n].toSpliced(1, -5, 9n)).toEqual([a, 9n, b, 0n])
    expect([a, b, 0n].toSpliced(1, undefined as unknown as number, 9n)).toEqual([a, 9n, b, 0n])
    expect([a, b].reduce((x, y) => x + y)).toBe(a + b)
    expect([a, b].reduceRight((x, y) => x - y)).toBe(b - a)
    expect(() => ([] as bigint[]).reduce((x, y) => x + y)).toThrow()
    expect([[[a]], [b]].flat(Infinity)).toEqual([a, b])
    expect([[[a]], [b]].flat(-Infinity)).toEqual([[[a]], [b]])
    expect(Math.min(i, Infinity)).toBe(i)
    expect(Math.max(i, -Infinity)).toBe(i)
    const m = new Map<string | undefined, bigint>([["x", a], ["y", b]])
    expect(m.has(k)).toBe(k !== undefined)
    expect(m.get(k)).toBe(k === "x" ? a : k === "y" ? b : undefined)
    let sum = 0n
    m.forEach(v => { sum += v })
    expect(sum).toBe(a + b)
    expect("A".codePointAt(0)).toBe(65)
    expect("A".codePointAt(5)).toBeUndefined()
    expect("7".padStart(3, pad)).toBe(`${pad}${pad}7`)
    expect(2 ** 10).toBe(1024)
    expect(10n ** 0n).toBe(1n)
    expect(a ** 2n).toBe(a * a)
    expect(() => 2n ** -1n).toThrow()
    expect(() => alwaysThrows() === 1n).toThrow()
    expect(() => !alwaysThrows()).toThrow()
  })

  law("FALSE: ordering matcher on unconditional throw reports throws instead of unsupported", () => {
    expect(alwaysThrows()).toBeGreaterThan(0n)
  })

  law("try/catch, conditional object spread, Object.assign, ES2025 Set methods, freeze and spread snapshotting", domain<{ items: [bigint] | [bigint, bigint]; a: bigint; b: bigint; flag: boolean }>(), ({ items, a, b, flag }) => {
    expect(items.length === 1 || items.length === 2).toBe(true)
    expect(safeDivide(a, b)).toBe(b === 0n ? 0n : a / b)
    let fallback = a
    try {
      if (b === 0n) throw new Error("zero")
    } catch {
      fallback = 0n
    }
    expect(fallback).toBe(b === 0n ? 0n : a)
    expect(mergeConfig(flag, a, b)).toEqual(flag ? { a, b } : { a })
    expect({ ...(flag ? { x: a } : null), y: b }).toEqual(flag ? { x: a, y: b } : { y: b })
    // Spread fields are snapshotted before later properties mutate the source.
    const src = { x: 1n }
    const snap = { ...src, y: (() => { src.x = 2n; return 9n })() }
    expect(snap).toEqual({ x: 1n, y: 9n })
    // Conditional Object.freeze stays on its own branch so the else branch can still write.
    const box = { v: a }
    if (flag) { Object.freeze(box) } else { box.v = b }
    expect(box.v).toBe(flag ? a : b)
    const s1 = new Set([a, b])
    const s2 = new Set([b])
    expect(s2.isSubsetOf(s1)).toBe(true)
    expect(s1.isSupersetOf(s2)).toBe(true)
    expect(s1.isDisjointFrom(s2)).toBe(false)
    const s3 = new Set([1n, 2n])
    s3.delete(flag ? 1n : 2n)
    expect(s3.size).toBe(1)
    const c1 = new Set(["a", "b"])
    const c2 = new Set(["b", "c"])
    expect([...c1.union(c2)]).toEqual(["a", "b", "c"])
    expect([...c1.intersection(c2)]).toEqual(["b"])
    expect([...c1.difference(c2)]).toEqual(["a"])
    expect([...c1.symmetricDifference(c2)]).toEqual(["a", "c"])
    expect(Math.pow(3, 2)).toBe(9)
    expect(new Set(null).size).toBe(0)
    // A non-throwing obligation after a throwing expression in `try` is guarded by the earlier throw not happening.
    const guarded = (() => {
      try {
        const q = 10n / a
        const r = Math.trunc(10 / (a === 0n ? 0 : 2))
        return q + BigInt(r)
      } catch {
        return 0n
      }
    })()
    expect(guarded).toBe(a === 0n ? 0n : 10n / a + 5n)
  })

  law("parenthesized arrow body expectation is not vacuous", domain<bigint>(), x => (expect(x + 0n).toBe(x)))

  law("CHECKED: try block mutating outer object before throwing is refused", domain<boolean>(), flag => {
    const box = { x: 0n }
    try {
      if (flag) {
        box.x = 1n
        throw new Error("boom")
      }
    } catch {
      // ignore
    }
    expect(box.x).toBe(flag ? 1n : 0n)
  })

  law("CHECKED: destructuring catch parameter is refused", domain<boolean>(), _flag => {
    let ok = false
    try {
      try {
        throw null
      } catch ({}: any) {
        ok = true
      }
    } catch {
      ok = false
    }
    expect(ok).toBe(false)
  })

  law("CHECKED: Object.assign adding keys in different orders across branches is refused", domain<boolean>(), flag => {
    const dst: Record<string, bigint> = {}
    Object.assign(dst, flag ? { a: 1n, b: 2n } : { b: 2n, a: 1n })
    expect(Object.keys(dst)).toEqual(flag ? ["a", "b"] : ["b", "a"])
  })

  law("CHECKED: Math.pow with spread leaving wrong arity is refused cleanly", domain<boolean>(), _flag => {
    const t: [number] = [3]
    t.pop()
    expect(Number.isNaN(Math.pow(...(t as unknown as [number]), 2))).toBe(true)
  })
})
