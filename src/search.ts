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
export function assignments(binders: readonly Binder[], strings: readonly string[], budget: number): Assignments {
  const pools = binders.map(b => b.domain ?? (b.ty === "int" ? INTEGERS : b.ty === "bool" ? [true, false] : strings))
  const total = pools.reduce((n, pool) => n * pool.length, 1)
  const finite = binders.every(b => b.domain)
  const grid = total <= budget
  return {
    exhaustive: finite && grid,
    each(visit) {
      const env = new Map<string, Scalar>()
      if (grid) {
        const index = pools.map(() => 0)
        for (let n = 0; n < total; n++) {
          binders.forEach((b, i) => env.set(b.name, pools[i]![index[i]!]!))
          if (visit(env)) return
          for (let i = pools.length - 1; i >= 0 && ++index[i]! === pools[i]!.length; i--) index[i] = 0
        }
      }
      if (finite && grid) return
      const random = generator(0x9e3779b9)
      const draws = Math.min(budget, 5_000)
      for (let n = 0; n < draws; n++) {
        binders.forEach((b, i) => {
          const pool = pools[i]!
          const fromPool = b.domain || b.ty !== "int" || random() < 0.2
          env.set(b.name, fromPool ? pool[Math.floor(random() * pool.length)]! : randomInteger(random))
        })
        if (visit(env)) return
      }
    },
  }
}

/** Strings worth trying for an unbounded string input: the literals in play and their pieces. */
export function stringPool(expressions: readonly Expr[]): string[] {
  const literals = new Set<string>()
  for (const e of expressions) ir.stringLiterals(e, literals)
  const pool = new Set(["", "a", "b", ...literals])
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

function truthy(e: Expr, env: Map<string, Scalar>): boolean {
  try {
    return ir.evaluate(e, env) === true
  } catch (error) {
    if (error instanceof ir.EvaluationError) return false
    throw error
  }
}

export function findInput(binders: readonly Binder[], condition: Expr): { found: Map<string, Scalar> | undefined; exhaustive: boolean } {
  if (condition === ir.TRUE) return { found: new Map(), exhaustive: true }
  const free = ir.freeVariables(condition)
  const used = binders.filter(b => free.has(b.name))
  const space = assignments(used, stringPool([condition]), SEARCH_BUDGET)
  let found: Map<string, Scalar> | undefined
  space.each(env => {
    if (!truthy(condition, env)) return false
    found = new Map(env)
    return true
  })
  return { found, exhaustive: space.exhaustive }
}

export function showInputs(binders: readonly Binder[], env: Map<string, Scalar>): Record<string, string> {
  const shown: Record<string, string> = {}
  for (const binder of binders) {
    const value = env.get(binder.name)
    if (value !== undefined) shown[binder.label] = ir.showScalar(value)
  }
  return shown
}

export function showValue(e: Expr, env: Map<string, Scalar>): string {
  try {
    return ir.showScalar(ir.evaluate(e, env))
  } catch {
    return "(throws)"
  }
}
