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

function register(name: string, second?: unknown, third?: unknown): void {
  const registry = (globalThis as Record<symbol, unknown>)[REGISTRY] as Registered[] | undefined
  const callback = (typeof second === "function" ? second : typeof third === "function" ? third : undefined) as Registered["callback"]
  registry?.push({ name, callback })
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

export const law: Law = Object.assign(register as LawFunction, { skip: register as LawFunction, only: register as LawFunction, todo: register })

export interface Describe {
  /** Group laws under a shared name. */
  (name: string, body: () => void): void
  skip(name: string, body: () => void): void
  only(name: string, body: () => void): void
}

const group = (_name: string, body: () => void) => body()
export const describe: Describe = Object.assign(group, { skip: group, only: group })

export class ExpectationFailed extends Error {}

function equal(a: unknown, b: unknown): boolean {
  if (Object.is(a, b)) return true
  if (typeof a !== "object" || typeof b !== "object" || a === null || b === null) return false
  if (Array.isArray(a) !== Array.isArray(b)) return false
  const keys = Object.keys(a)
  if (keys.length !== Object.keys(b).length) return false
  return keys.every(key => Object.hasOwn(b, key) && equal((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]))
}

function matchers<T>(actual: T, negated: boolean): Matchers<T> {
  const check = (pass: boolean) => {
    if (pass === negated) throw new ExpectationFailed("expectation failed")
  }
  return {
    toEqual: expected => check(equal(actual, expected)),
    toBe: expected => check(Object.is(actual, expected)),
    get not() {
      return matchers(actual, !negated)
    },
  }
}

export function expect<T>(actual: T): Matchers<T> {
  return matchers(actual, false)
}
