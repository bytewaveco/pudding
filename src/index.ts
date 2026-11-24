export interface Config {
  include?: string[]
  exclude?: string[]
  tsconfig?: string
  strict?: boolean
  crossCheck?: boolean
  cache?: boolean
  lean?: string
  reporter?: 'default' | 'verbose' | 'json' | 'github'
}

export function defineConfig(config: Config): Config {
  return config
}

export type Integer<Min extends number = number, Max extends number = number> = number & {
  readonly __puddingInteger?: [Min, Max]
}

export interface Domain<T> {
  readonly value: T
}

export interface LawOptions {
  proof?: string
}

export interface Matchers<T> {
  toEqual(expected: NoInfer<T>): void
  toBe(expected: NoInfer<T>): void
  toBeGreaterThan(
    expected: T extends number ? number : T extends bigint ? bigint : number | bigint,
  ): void
  toBeGreaterThanOrEqual(
    expected: T extends number ? number : T extends bigint ? bigint : number | bigint,
  ): void
  toBeLessThan(
    expected: T extends number ? number : T extends bigint ? bigint : number | bigint,
  ): void
  toBeLessThanOrEqual(
    expected: T extends number ? number : T extends bigint ? bigint : number | bigint,
  ): void
  toBeUndefined(): void
  toBeDefined(): void
  toBeNull(): void
  toBeTruthy(): void
  toBeFalsy(): void
  toHaveLength(expected: number): void
  toContain(expected: unknown): void
  toThrow(): void
  readonly not: Matchers<T>
}

interface Registered {
  name: string
  callback: ((input: unknown) => void) | undefined
}

const REGISTRY = Symbol.for('pudding.registry')

export function domain<T>(): Domain<T> {
  return {} as Domain<T>
}

type Modifier = 'run' | 'skip' | 'only' | 'todo'

const registry = () => (globalThis as Record<symbol, unknown>)[REGISTRY] as Registered[] | undefined
const bridge =
  typeof process !== 'undefined' && process.env['VITEST'] !== undefined && !registry()
    ? await import('./vitest.ts').catch(() => undefined)
    : undefined
const vitest = bridge?.collecting() ? bridge : undefined

const register =
  (modifier: Modifier) =>
  (name: string, second?: unknown, third?: unknown): void => {
    const collected = registry()
    const callback = (
      typeof second === 'function' ? second : typeof third === 'function' ? third : undefined
    ) as Registered['callback']

    if (collected) collected.push({ name, callback })
    else vitest?.defineLaw(modifier, name)
  }

export interface LawFunction {
  <T>(name: string, inputs: Domain<T>, check: (input: T) => void, options?: LawOptions): void
  (name: string, check: () => void, options?: LawOptions): void
}

export interface Law extends LawFunction {
  skip: LawFunction
  only: LawFunction
  todo(name: string): void
}

export const law: Law = Object.assign(register('run') as LawFunction, {
  skip: register('skip') as LawFunction,
  only: register('only') as LawFunction,
  todo: register('todo') as (name: string) => void,
})

export interface Describe {
  (name: string, body: () => void): void
  skip(name: string, body: () => void): void
  only(name: string, body: () => void): void
}

const group =
  (modifier: 'run' | 'skip' | 'only') =>
  (name: string, body: () => void): void => {
    if (vitest && !registry()) vitest.defineGroup(modifier, name, body)
    else body()
  }

export const describe: Describe = Object.assign(group('run'), {
  skip: group('skip'),
  only: group('only'),
})

export class ExpectationFailed extends Error {}

function equal(a: unknown, b: unknown): boolean {
  if (a === b || Object.is(a, b)) return true
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false

  const paired = (left: unknown[], right: unknown[]) => {
    const free = [...right]
    return (
      left.length === right.length &&
      left.every((item) => {
        const match = free.findIndex((other) => equal(item, other))
        if (match >= 0) free.splice(match, 1)
        return match >= 0
      })
    )
  }

  if (a instanceof Map || b instanceof Map)
    return a instanceof Map && b instanceof Map && paired([...a], [...b])

  if (a instanceof Set || b instanceof Set)
    return a instanceof Set && b instanceof Set && paired([...a], [...b])

  if (a instanceof Date || b instanceof Date)
    return a instanceof Date && b instanceof Date && a.getTime() === b.getTime()

  if (Array.isArray(a) !== Array.isArray(b)) return false
  const keys = Object.keys(a)
  if (keys.length !== Object.keys(b).length) return false

  const plain = (value: object) =>
    Array.isArray(value) ||
    Object.getPrototypeOf(value) === Object.prototype ||
    Object.getPrototypeOf(value) === null

  if (keys.length === 0 && (!plain(a) || !plain(b))) return false
  return keys.every(
    (key) =>
      Object.hasOwn(b, key) &&
      equal((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]),
  )
}

function matchers<T>(actual: T, negated: boolean): Matchers<T> {
  const check = (pass: boolean) => {
    if (pass === negated) throw new ExpectationFailed('expectation failed')
  }

  const ordered = (
    expected: unknown,
    compare: (a: number | bigint, b: number | bigint) => boolean,
  ) => {
    if (
      typeof actual !== typeof expected ||
      (typeof actual !== 'number' && typeof actual !== 'bigint')
    )
      return false

    return compare(actual as number | bigint, expected as number | bigint)
  }

  return {
    toEqual: (expected) => check(equal(actual, expected)),
    toBe: (expected) => check(actual === expected || Object.is(actual, expected)),
    toBeGreaterThan: (expected) => check(ordered(expected, (a, b) => a > b)),
    toBeGreaterThanOrEqual: (expected) => check(ordered(expected, (a, b) => a >= b)),
    toBeLessThan: (expected) => check(ordered(expected, (a, b) => a < b)),
    toBeLessThanOrEqual: (expected) => check(ordered(expected, (a, b) => a <= b)),
    toBeUndefined: () => check(actual === undefined),
    toBeDefined: () => check(actual !== undefined),
    toBeNull: () => check(actual === null),
    toBeTruthy: () => check(Boolean(actual)),
    toBeFalsy: () => check(!actual),
    toHaveLength: (expected) =>
      check((Array.isArray(actual) || typeof actual === 'string') && actual.length === expected),
    toContain: (expected) =>
      check(
        Array.isArray(actual)
          ? actual.includes(expected)
          : typeof actual === 'string' && typeof expected === 'string' && actual.includes(expected),
      ),
    toThrow: () => {
      if (typeof actual !== 'function') throw new ExpectationFailed('expected a function')
      let threw = false

      try {
        ;(actual as () => unknown)()
      } catch {
        threw = true
      }

      check(threw)
    },
    get not() {
      return matchers(actual, !negated)
    },
  }
}

export function expect<T>(actual: T): Matchers<T> {
  return matchers(actual, false)
}
