// The API that law files import.
//
// Pudding proves laws by reading them, not by running them. These functions
// still work at run time so the runner can execute a law against the real
// code and compare the result with the model it proved things about.

export interface Config {
  /** Globs of law files, relative to the project. Default: every `*.law.ts`. */
  include?: string[]
  /** Globs to leave out. `node_modules` is always left out. */
  exclude?: string[]
  /**
   * The tsconfig whose compiler options (paths, module resolution, strictness)
   * the law files are read with. Default: `tsconfig.json` when it exists. The
   * law files do not have to be included by it.
   */
  tsconfig?: string
  /** Fail when a law is checked by execution only, without a proof. */
  strict?: boolean
  /** Execute each law against the real code and compare it with the proved model. Default: true. */
  crossCheck?: boolean
  /** Reuse results from earlier runs. Default: true. */
  cache?: boolean
  /** Path of the Lean binary. */
  lean?: string
  /** How results are printed. Default: `default`, or `github` inside GitHub Actions. */
  reporter?: "default" | "verbose" | "json" | "github"
}

export function defineConfig(config: Config): Config {
  return config
}

/**
 * A whole number. As a law input it means every integer from `Min` to `Max`,
 * or every integer a `number` holds exactly when no bounds are given. A plain
 * `number` cannot be an input, because it also covers fractions, NaN and
 * infinities, which are not modeled.
 */
export type Integer<Min extends number = number, Max extends number = number> = number & { readonly __puddingInteger?: [Min, Max] }

export interface Domain<T> {
  readonly value: T
}

export interface LawOptions {
  /**
   * A Lean tactic script used in place of the default automation for the
   * obligations of this law that range over unbounded inputs.
   */
  proof?: string
}

export interface Matchers<T> {
  /** Structural equality. */
  toEqual(expected: NoInfer<T>): void
  /** Equality of booleans, bigints and strings. */
  toBe(expected: NoInfer<T>): void
  readonly not: Matchers<T>
}

interface Registered {
  name: string
  callback: ((input: unknown) => void) | undefined
}

const REGISTRY = Symbol.for("pudding.registry")

/** Describe every value of `T`. The type argument is read by the prover. */
export function domain<T>(): Domain<T> {
  return {} as Domain<T>
}

type Modifier = "run" | "skip" | "only" | "todo"

/**
 * A law file can be loaded in three ways. Pudding's own runner loads it with a
 * registry in place, to execute the laws against the real code. Vitest loads
 * it as a test file, and each law becomes a test that reports its proof.
 * Anything else, such as importing it by accident, does nothing.
 */
const registry = () => (globalThis as Record<symbol, unknown>)[REGISTRY] as Registered[] | undefined
const bridge = typeof process !== "undefined" && process.env["VITEST"] !== undefined && !registry() ? await import("./vitest.ts").catch(() => undefined) : undefined
const vitest = bridge?.collecting() ? bridge : undefined

const register = (modifier: Modifier) => (name: string, second?: unknown, third?: unknown): void => {
  const collected = registry()
  const callback = (typeof second === "function" ? second : typeof third === "function" ? third : undefined) as Registered["callback"]
  if (collected) collected.push({ name, callback })
  else vitest?.defineLaw(modifier, name)
}

export interface LawFunction {
  /** State a law that must hold for every value of the domain. */
  <T>(name: string, inputs: Domain<T>, check: (input: T) => void, options?: LawOptions): void
  /** State a law about fixed values. */
  (name: string, check: () => void, options?: LawOptions): void
}

export interface Law extends LawFunction {
  /** List the law without checking it. */
  skip: LawFunction
  /** Check only the laws of this file that are marked `only`. */
  only: LawFunction
  /** Record a law that is still to be written. */
  todo(name: string): void
}

export const law: Law = Object.assign(register("run") as LawFunction, {
  skip: register("skip") as LawFunction, only: register("only") as LawFunction, todo: register("todo") as (name: string) => void,
})

export interface Describe {
  /** Group laws under a shared name. */
  (name: string, body: () => void): void
  skip(name: string, body: () => void): void
  only(name: string, body: () => void): void
}

const group = (modifier: "run" | "skip" | "only") => (name: string, body: () => void): void => {
  if (vitest && !registry()) vitest.defineGroup(modifier, name, body)
  else body()
}
export const describe: Describe = Object.assign(group("run"), { skip: group("skip"), only: group("only") })

export class ExpectationFailed extends Error {}

// Zero and negative zero are treated as equal, as `===` treats them: whole
// numbers are modeled as integers, which have a single zero.
function equal(a: unknown, b: unknown): boolean {
  if (a === b || Object.is(a, b)) return true
  if (typeof a !== "object" || typeof b !== "object" || a === null || b === null) return false
  // A Map or a Set keeps what it holds out of its own properties, so it is compared by its entries:
  // each one has to pair up with one of the other side that equals it, whatever the order.
  const paired = (left: unknown[], right: unknown[]) => {
    const free = [...right]
    return left.length === right.length && left.every(item => {
      const match = free.findIndex(other => equal(item, other))
      if (match >= 0) free.splice(match, 1)
      return match >= 0
    })
  }
  if (a instanceof Map || b instanceof Map) return a instanceof Map && b instanceof Map && paired([...a], [...b])
  if (a instanceof Set || b instanceof Set) return a instanceof Set && b instanceof Set && paired([...a], [...b])
  if (a instanceof Date || b instanceof Date) return a instanceof Date && b instanceof Date && a.getTime() === b.getTime()
  if (Array.isArray(a) !== Array.isArray(b)) return false
  const keys = Object.keys(a)
  if (keys.length !== Object.keys(b).length) return false
  // Something that keeps what it holds out of its own properties, such as a RegExp, shows nothing to compare: it only equals itself.
  const plain = (value: object) => Array.isArray(value) || Object.getPrototypeOf(value) === Object.prototype || Object.getPrototypeOf(value) === null
  if (keys.length === 0 && (!plain(a) || !plain(b))) return false
  return keys.every(key => Object.hasOwn(b, key) && equal((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]))
}

function matchers<T>(actual: T, negated: boolean): Matchers<T> {
  const check = (pass: boolean) => {
    if (pass === negated) throw new ExpectationFailed("expectation failed")
  }
  return {
    toEqual: expected => check(equal(actual, expected)),
    toBe: expected => check(actual === expected || Object.is(actual, expected)),
    get not() {
      return matchers(actual, !negated)
    },
  }
}

export function expect<T>(actual: T): Matchers<T> {
  return matchers(actual, false)
}
