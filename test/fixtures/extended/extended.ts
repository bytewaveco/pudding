export function nullOrDefault(value: bigint | null, fallback: bigint): bigint {
  return value ?? fallback
}

export function paramDefault(value: bigint | null | undefined = 10n): bigint | null {
  return value
}

export function nullAccess(box: { v: bigint } | null): bigint {
  return (box as { v: bigint }).v
}

export function optionalNull(box: { inner: { v: bigint } | null } | null): bigint | undefined {
  return box?.inner?.v
}

export function tagOf(x: bigint | string | boolean | null | undefined): string {
  if (x === null) return "null"
  return typeof x
}

export function hasField(obj: { a: bigint; b?: bigint }, key: "a" | "b" | "c"): boolean {
  return key in obj
}

export function orderedKeys(a: bigint, b: bigint): string[] {
  return Object.keys({ z: a, "2": b, a: a, "0": b })
}

export function roundTripEntries(a: bigint, b: bigint): { a: bigint; b: bigint } {
  const entries = Object.entries({ a, b })
  return Object.fromEntries(entries) as { a: bigint; b: bigint }
}

export function sumVariadic(...nums: bigint[]): bigint {
  return nums.reduce((acc, n) => acc + n, 0n)
}

export function minOfList(xs: readonly number[]): number {
  return Math.min(...xs)
}

export function listOps(a: bigint, b: bigint, c: bigint) {
  const base = [a].concat([b, c])
  const rev = base.toReversed()
  const idx = base.indexOf(b)
  const lastIdx = base.lastIndexOf(b)
  const foundIdx = base.findIndex(x => x > 0n)
  const foundLast = base.findLast(x => x > 0n)
  const foundLastIdx = base.findLastIndex(x => x > 0n)
  const joined = [a, null, undefined, b].join(":")
  const flattened = [[a], [b, c]].flat()
  const rightOrder = [a, b, c].reduceRight((acc, x) => acc + String(x), "")
  let total = 0n
  base.forEach(x => { total += x })
  return { rev, idx, lastIdx, foundIdx, foundLast, foundLastIdx, joined, flattened, rightOrder, total }
}

export function stackOps(a: bigint, b: bigint) {
  const arr = [a]
  arr.unshift(b)
  const top = arr.pop()
  const head = arr.shift()
  return { top, head, remaining: arr.length }
}

export function mapDeleteOrder(a: bigint, b: bigint, c: bigint) {
  const m = new Map<string, bigint>([["x", a], ["y", b]])
  const removed = m.delete("x")
  const missing = m.delete("z")
  m.set("x", c)
  return { removed, missing, keys: [...m.keys()], values: [...m.values()], size: m.size, x: m.get("x") }
}

export function mapSymbolicDelete(k1: bigint, k2: bigint, v: bigint) {
  const m = new Map<bigint, bigint>()
  m.set(k1, v)
  const existed = m.delete(k2)
  return { existed, hasK1: m.has(k1), size: m.size }
}

export function stringHelpers(name: "ada" | "grace", raw: string) {
  const initial = name.slice(0, 1).toUpperCase()
  const parts = `  ${name}-ok  `.trim().split("-")
  const replaced = name.replace("a", "A")
  const replacedAll = name.replaceAll("a", "A")
  const prefixed = ("pre_" + raw).startsWith("pre_")
  const suffixed = (raw + "_end").endsWith("_end")
  const includesMid = (raw + "MID" + raw).includes("MID")
  return { initial, parts, replaced, replacedAll, prefixed, suffixed, includesMid }
}

export function requirePositive(x: bigint): bigint {
  if (x <= 0n) throw new Error("must be positive")
  return x
}

export const FROZEN_DAYS = Object.freeze([31, 28, 31, 30])

export function daysOrDefault(month: number): number {
  return FROZEN_DAYS.at(month) ?? 0
}

export function alwaysThrows(): bigint {
  throw Error("always")
}

export function safeDivide(a: bigint, b: bigint): bigint {
  try {
    return a / b
  } catch {
    return 0n
  }
}

export function mergeConfig(flag: boolean, a: bigint, b: bigint): { a: bigint; b?: bigint } {
  const extra = flag ? { b } : null
  return Object.assign({}, { a }, extra)
}
