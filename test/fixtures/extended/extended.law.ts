import { describe, domain, expect, law, type Integer } from "@bytewaveco/pudding"
import {
  hasField, listOps, mapDeleteOrder, mapSymbolicDelete, minOfList, nullAccess, nullOrDefault,
  optionalNull, orderedKeys, paramDefault, requirePositive, roundTripEntries, stackOps,
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
})
