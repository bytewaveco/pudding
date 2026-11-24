import * as ir from './ir.ts'

import type { Binder, Expr, Scalar } from './ir.ts'

const SEARCH_BUDGET = 60_000

function generator(seed: number) {
  return () => {
    seed = (seed + 0x6d2b79f5) | 0
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

const INTEGERS = [
  0n,
  1n,
  -1n,
  2n,
  -2n,
  3n,
  -3n,
  5n,
  7n,
  10n,
  -10n,
  99n,
  100n,
  -100n,
  101n,
  2n ** 31n,
  -(2n ** 31n),
  2n ** 53n + 1n,
]

function randomInteger(random: () => number): bigint {
  const kind = random()
  if (kind < 0.5) return BigInt(Math.floor(random() * 41) - 20)
  if (kind < 0.85) return BigInt(Math.floor(random() * 2_000_001) - 1_000_000)
  return BigInt(Math.floor((random() - 0.5) * 2 ** 53)) * BigInt(Math.floor(random() * 2 ** 20) + 1)
}

export interface Assignments {
  exhaustive: boolean
  each(visit: (env: Map<string, Scalar>) => boolean | void): void
}

export function assignments(binders: readonly Binder[], pool: Pool, budget: number): Assignments {
  const strings = pool.strings

  const integers = (b: Binder): readonly Scalar[] => {
    const [low, high] = b.range ?? [undefined, undefined]
    const edges = low === undefined ? [] : [low, low + 1n, high - 1n, high, (low + high) / 2n]
    return [
      ...new Set(
        [...INTEGERS, ...pool.integers, ...edges].filter(
          (value) => low === undefined || (value >= low && value <= high),
        ),
      ),
    ]
  }

  const elemPool = (b: Binder): readonly Scalar[] =>
    b.ty === 'list_bool' ? [true, false] : b.ty === 'list_str' ? strings : integers(b)

  const listPool = (b: Binder): readonly Scalar[] => {
    const elems = elemPool(b)
    const e0 = elems[0]!,
      e1 = elems[1] ?? e0,
      e2 = elems[2] ?? e0,
      e3 = elems[3] ?? e1
    const base: Scalar[] = [
      [],
      [e0],
      [e1],
      [e0, e1],
      [e1, e0],
      [e0, e0],
      [e0, e1, e2],
      [e2, e1, e0],
      [e0, e1, e2, e3, e0],
    ]

    for (const len of [10, 25, 50]) {
      const long: Scalar[] = []
      for (let i = 0; i < len; i++) long.push(elems[i % elems.length]!)
      base.push(long)
    }

    return base
  }

  const randomList = (b: Binder, random: () => number): Scalar[] => {
    const elems = elemPool(b)
    const r = random()
    const len =
      r < 0.15
        ? 0
        : r < 0.65
          ? 1 + Math.floor(random() * 5)
          : r < 0.9
            ? 6 + Math.floor(random() * 15)
            : 20 + Math.floor(random() * 40)
    const out: Scalar[] = []

    for (let i = 0; i < len; i++) {
      if (b.ty === 'list_int' && random() >= 0.4) {
        const v = randomInteger(random)
        const inside = !b.range || (v >= b.range[0] && v <= b.range[1])
        out.push(inside ? v : elems[Math.floor(random() * elems.length)]!)
      } else {
        out.push(elems[Math.floor(random() * elems.length)]!)
      }
    }

    return out
  }

  const pools = binders.map(
    (b) =>
      b.domain ??
      (ir.isListTy(b.ty)
        ? listPool(b)
        : b.ty === 'int'
          ? integers(b)
          : b.ty === 'bool'
            ? [true, false]
            : strings),
  )
  const total = pools.reduce((n, pool) => n * pool.length, 1)
  const finite = binders.every((b) => b.domain)
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

          for (let i = pools.length - 1; i >= 0 && ++index[i]! === pools[i]!.length; i--)
            index[i] = 0
        }
      } else if (pools.length) {
        const maxPool = Math.min(32, Math.max(...pools.map((p) => p.length)))

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

          if (ir.isListTy(b.ty)) {
            env.set(
              b.name,
              random() < 0.25 ? pool[Math.floor(random() * pool.length)]! : randomList(b, random),
            )
            return
          }

          const fromPool = b.domain || b.ty !== 'int' || random() < 0.2
          const drawn = fromPool ? pool[Math.floor(random() * pool.length)]! : randomInteger(random)
          const inside =
            !b.range || typeof drawn !== 'bigint' || (drawn >= b.range[0] && drawn <= b.range[1])
          env.set(b.name, inside ? drawn : pool[Math.floor(random() * pool.length)]!)
        })
        if (visit(env)) return
      }
    },
  }
}

export interface Pool {
  strings: string[]
  integers: bigint[]
}

export function valuePool(expressions: readonly Expr[]): Pool {
  const literals = new Set<bigint>()
  for (const e of expressions) ir.integerLiterals(e, literals)
  const integers = [...literals].slice(0, 64).flatMap((value) => [value, value - 1n, value + 1n])
  return { strings: stringPool(expressions), integers }
}

function stringPool(expressions: readonly Expr[]): string[] {
  const literals = new Set<string>()
  for (const e of expressions) ir.stringLiterals(e, literals)
  const pool = new Set(['', 'a', 'b', 'é', '😀', ...literals])

  for (const literal of literals) {
    for (const token of literal.split(/[^\p{L}\p{N}]+/u)) pool.add(token)
    const chars = [...literal]

    for (let n = 1; n < chars.length && n <= 12; n++) {
      pool.add(chars.slice(0, n).join(''))
      pool.add(chars.slice(-n).join(''))
    }
  }

  return [...pool].slice(0, 96)
}

function truthyFn(
  evalCond: (env: ReadonlyMap<string, Scalar>) => Scalar,
): (env: Map<string, Scalar>) => boolean {
  return (env) => {
    try {
      return evalCond(env) === true
    } catch (error) {
      if (error instanceof ir.EvaluationError) return false
      throw error
    }
  }
}

function shrink(
  binders: readonly Binder[],
  holds: (env: Map<string, Scalar>) => boolean,
  initial: Map<string, Scalar>,
): Map<string, Scalar> {
  const cur = new Map(initial)

  for (let pass = 0; pass < 3; pass++) {
    let improved = false

    for (const b of binders) {
      if (b.domain) continue
      const current = cur.get(b.name)

      if (b.ty === 'int' && typeof current === 'bigint') {
        const [lo, hi] = b.range ?? [undefined, undefined]
        const inRange = (v: bigint) => lo === undefined || (v >= lo && v <= hi!)
        const target = lo !== undefined && lo > 0n ? lo : hi !== undefined && hi < 0n ? hi : 0n
        if (current === target) continue

        if (inRange(target)) {
          cur.set(b.name, target)

          if (holds(cur)) {
            improved = true
            continue
          }

          cur.set(b.name, current)
        }

        let low = target
        let high = current

        while (low !== high) {
          const mid = low + (high - low) / 2n
          if (mid === low || mid === high) break
          cur.set(b.name, mid)

          if (inRange(mid) && holds(cur)) {
            high = mid
            improved = true
          } else {
            cur.set(b.name, high)
            low = mid
          }
        }

        cur.set(b.name, high)
      } else if (b.ty === 'str' && typeof current === 'string' && current.length > 0) {
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

        if (tryStr('')) continue
        let best = [...bestStr]

        for (let len = Math.floor(best.length / 2); len >= 1; len = Math.floor(len / 2)) {
          if (tryStr(best.slice(0, len).join(''))) best = best.slice(0, len)
          else if (tryStr(best.slice(-len).join(''))) best = best.slice(-len)
        }

        for (let step = 0; step < 16 && best.length > 1; step++) {
          if (tryStr(best.slice(0, -1).join(''))) best = best.slice(0, -1)
          else if (tryStr(best.slice(1).join(''))) best = best.slice(1)
          else break
        }
      } else if (ir.isListTy(b.ty) && Array.isArray(current) && current.length > 0) {
        let bestList: readonly Scalar[] = current

        const tryList = (candidate: readonly Scalar[]) => {
          cur.set(b.name, candidate)

          if (holds(cur)) {
            bestList = candidate
            improved = true
            return true
          }

          cur.set(b.name, bestList)
          return false
        }

        if (tryList([])) continue

        for (let len = Math.floor(bestList.length / 2); len >= 1; len = Math.floor(len / 2)) {
          if (tryList(bestList.slice(0, len))) continue
          tryList(bestList.slice(-len))
        }

        for (let step = 0; step < 16 && bestList.length > 1; step++) {
          if (tryList(bestList.slice(0, -1))) continue
          if (tryList(bestList.slice(1))) continue
          break
        }
      }
    }

    if (!improved) break
  }

  return cur
}

export function findInput(
  binders: readonly Binder[],
  condition: Expr,
  defs?: ReadonlyMap<string, ir.FnDef>,
): { found: Map<string, Scalar> | undefined; exhaustive: boolean } {
  if (condition === ir.TRUE) return { found: new Map(), exhaustive: true }
  const free = ir.freeVariables(condition)
  const used = binders.filter((b) => free.has(b.name))
  const holds = truthyFn(ir.compile(condition, defs))
  const space = assignments(used, valuePool([condition]), SEARCH_BUDGET)
  let found: Map<string, Scalar> | undefined
  space.each((env) => {
    if (!holds(env)) return false
    found = new Map(env)
    return true
  })
  if (found && !space.exhaustive) found = shrink(used, holds, found)
  return { found, exhaustive: space.exhaustive }
}

export function showInputs(
  binders: readonly Binder[],
  env: Map<string, Scalar>,
): Record<string, string> {
  const shown: Record<string, string> = {}

  for (const binder of binders) {
    const value = env.get(binder.name)
    if (value !== undefined) shown[binder.label] = ir.showScalar(value, binder.num)
  }

  return shown
}

export function showValue(
  e: Expr,
  env: Map<string, Scalar>,
  num = false,
  defs?: ReadonlyMap<string, ir.FnDef>,
): string {
  try {
    return ir.showScalar(ir.evaluate(e, env, defs), num)
  } catch {
    return '(throws)'
  }
}
