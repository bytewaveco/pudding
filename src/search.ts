// Choosing inputs to try: for counterexamples, for witnesses that a condition
// can hold, and for executing laws against the real code. Nothing here ever
// accepts a law; it only explains verdicts and looks for disagreement.

import * as ir from "./ir.ts"
import type { Binder, Expr, Scalar } from "./ir.ts"

const SEARCH_BUDGET = 60_000

function generator(seed: number) {
  return () => {
    seed = (seed + 0x6d2b79f5) | 0
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

const INTEGERS = [0n, 1n, -1n, 2n, -2n, 3n, -3n, 5n, 7n, 10n, -10n, 99n, 100n, -100n, 101n, 2n ** 31n, -(2n ** 31n), 2n ** 53n + 1n]

function randomInteger(random: () => number): bigint {
  const kind = random()
  if (kind < 0.5) return BigInt(Math.floor(random() * 41) - 20)
  if (kind < 0.85) return BigInt(Math.floor(random() * 2_000_001) - 1_000_000)
  return BigInt(Math.floor((random() - 0.5) * 2 ** 53)) * BigInt(Math.floor(random() * 2 ** 20) + 1)
}

export interface Assignments {
  /** True when every possible input is visited. */
  exhaustive: boolean
  each(visit: (env: Map<string, Scalar>) => boolean | void): void
}

/** Inputs to try: every combination when the space is small enough, otherwise a sample. */
export function assignments(binders: readonly Binder[], pool: Pool, budget: number): Assignments {
  const strings = pool.strings
  const integers = (b: Binder): readonly Scalar[] => {
    const [low, high] = b.range ?? [undefined, undefined]
    const edges = low === undefined ? [] : [low, low + 1n, high - 1n, high, (low + high) / 2n]
    return [...new Set([...INTEGERS, ...pool.integers, ...edges].filter(value => low === undefined || (value >= low && value <= high)))]
  }
  const pools = binders.map(b => b.domain ?? (b.ty === "int" ? integers(b) : b.ty === "bool" ? [true, false] : strings))
  const total = pools.reduce((n, pool) => n * pool.length, 1)
  const finite = binders.every(b => b.domain)
  // Keep grid + random draws within `budget`: for unbounded spaces leave room for random exploration.
  const grid = finite ? total <= budget : total <= Math.floor(budget * 0.6)
  return {
    exhaustive: finite && grid,
    each(visit) {
      const env = new Map<string, Scalar>()
      let ran = 0
      if (grid) {
        const index = pools.map(() => 0)
        for (let n = 0; n < total; n++) {
          binders.forEach((b, i) => env.set(b.name, pools[i]![index[i]!]!))
          ran++
          if (visit(env)) return
          for (let i = pools.length - 1; i >= 0 && ++index[i]! === pools[i]!.length; i--) index[i] = 0
        }
      } else if (pools.length) {
        // When the full grid is too large, probe synchronized pool entries (e.g. all 0s, 1s, literals) before random draws.
        const maxPool = Math.min(32, Math.max(...pools.map(p => p.length)))
        for (let k = 0; k < maxPool && ran < budget; k++) {
          binders.forEach((b, i) => env.set(b.name, pools[i]![k % pools[i]!.length]!))
          ran++
          if (visit(env)) return
        }
      }
      if (finite && grid) return
      const random = generator(0x9e3779b9)
      const draws = Math.max(0, Math.min(budget - ran, 25_000))
      for (let n = 0; n < draws; n++) {
        binders.forEach((b, i) => {
          const pool = pools[i]!
          const fromPool = b.domain || b.ty !== "int" || random() < 0.2
          const drawn = fromPool ? pool[Math.floor(random() * pool.length)]! : randomInteger(random)
          // A value outside an input's bounds is not an input at all.
          const inside = !b.range || typeof drawn !== "bigint" || (drawn >= b.range[0] && drawn <= b.range[1])
          env.set(b.name, inside ? drawn : pool[Math.floor(random() * pool.length)]!)
        })
        if (visit(env)) return
      }
    },
  }
}

/** Values worth trying for unbounded inputs, beyond the standard ones. */
export interface Pool {
  strings: string[]
  integers: bigint[]
}

/**
 * The constants a law mentions and their neighbours. A condition such as
 * `n === 424242n` is only ever true at a value no generic sample contains.
 */
export function valuePool(expressions: readonly Expr[]): Pool {
  const literals = new Set<bigint>()
  for (const e of expressions) ir.integerLiterals(e, literals)
  const integers = [...literals].slice(0, 64).flatMap(value => [value, value - 1n, value + 1n])
  return { strings: stringPool(expressions), integers }
}

/** Strings worth trying for an unbounded string input: the literals in play and their pieces. */
function stringPool(expressions: readonly Expr[]): string[] {
  const literals = new Set<string>()
  for (const e of expressions) ir.stringLiterals(e, literals)
  const pool = new Set(["", "a", "b", "é", "😀", ...literals])
  for (const literal of literals) {
    for (const token of literal.split(/[^\p{L}\p{N}]+/u)) pool.add(token)
    const chars = [...literal]
    for (let n = 1; n < chars.length && n <= 12; n++) {
      pool.add(chars.slice(0, n).join(""))
      pool.add(chars.slice(-n).join(""))
    }
  }
  return [...pool].slice(0, 96)
}

function truthyFn(evalCond: (env: ReadonlyMap<string, Scalar>) => Scalar): (env: Map<string, Scalar>) => boolean {
  return env => {
    try {
      return evalCond(env) === true
    } catch (error) {
      if (error instanceof ir.EvaluationError) return false
      throw error
    }
  }
}

/** Shrink a found counterexample toward simpler values (0 / bounds for ints, shorter text for strings). */
function shrink(binders: readonly Binder[], holds: (env: Map<string, Scalar>) => boolean, initial: Map<string, Scalar>): Map<string, Scalar> {
  const cur = new Map(initial)
  for (let pass = 0; pass < 3; pass++) {
    let improved = false
    for (const b of binders) {
      if (b.domain) continue
      const current = cur.get(b.name)
      if (b.ty === "int" && typeof current === "bigint") {
        const [lo, hi] = b.range ?? [undefined, undefined]
        const inRange = (v: bigint) => lo === undefined || (v >= lo && v <= hi!)
        const target = lo !== undefined && lo > 0n ? lo : hi !== undefined && hi < 0n ? hi : 0n
        if (current === target) continue
        if (inRange(target)) {
          cur.set(b.name, target)
          if (holds(cur)) { improved = true; continue }
          cur.set(b.name, current)
        }
        let low = target
        let high = current
        while (low !== high) {
          const mid = low + (high - low) / 2n
          if (mid === low || mid === high) break
          cur.set(b.name, mid)
          if (inRange(mid) && holds(cur)) { high = mid; improved = true }
          else { cur.set(b.name, high); low = mid }
        }
        cur.set(b.name, high)
      } else if (b.ty === "str" && typeof current === "string" && current.length > 0) {
        let bestStr = current
        const tryStr = (candidate: string) => {
          cur.set(b.name, candidate)
          if (holds(cur)) {
            bestStr = candidate
            improved = true
            return true
          }
          cur.set(b.name, bestStr)
          return false
        }
        if (tryStr("")) continue
        let best = [...bestStr]
        for (let len = Math.floor(best.length / 2); len >= 1; len = Math.floor(len / 2)) {
          if (tryStr(best.slice(0, len).join(""))) best = best.slice(0, len)
          else if (tryStr(best.slice(-len).join(""))) best = best.slice(-len)
        }
        for (let step = 0; step < 16 && best.length > 1; step++) {
          if (tryStr(best.slice(0, -1).join(""))) best = best.slice(0, -1)
          else if (tryStr(best.slice(1).join(""))) best = best.slice(1)
          else break
        }
      }
    }
    if (!improved) break
  }
  return cur
}

export function findInput(binders: readonly Binder[], condition: Expr): { found: Map<string, Scalar> | undefined; exhaustive: boolean } {
  if (condition === ir.TRUE) return { found: new Map(), exhaustive: true }
  const free = ir.freeVariables(condition)
  const used = binders.filter(b => free.has(b.name))
  const holds = truthyFn(ir.compile(condition))
  const space = assignments(used, valuePool([condition]), SEARCH_BUDGET)
  let found: Map<string, Scalar> | undefined
  space.each(env => {
    if (!holds(env)) return false
    found = new Map(env)
    return true
  })
  if (found && !space.exhaustive) found = shrink(used, holds, found)
  return { found, exhaustive: space.exhaustive }
}

export function showInputs(binders: readonly Binder[], env: Map<string, Scalar>): Record<string, string> {
  const shown: Record<string, string> = {}
  for (const binder of binders) {
    const value = env.get(binder.name)
    if (value !== undefined) shown[binder.label] = ir.showScalar(value, binder.num)
  }
  return shown
}

export function showValue(e: Expr, env: Map<string, Scalar>, num = false): string {
  try {
    return ir.showScalar(ir.evaluate(e, env), num)
  } catch {
    return "(throws)"
  }
}
