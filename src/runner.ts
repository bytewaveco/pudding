// Orchestrates a run: read the laws with the TypeScript compiler, prove the
// resulting obligations in Lean, explain what failed, and compare the proved
// model with the real code.

import { execFileSync } from "node:child_process"
import { createHash } from "node:crypto"
import { existsSync, globSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs"
import { homedir } from "node:os"
import { dirname, isAbsolute, join, relative, resolve } from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"
import { API, DiagnosticCategory } from "typescript/unstable/sync"
import type { Config } from "./index.ts"
import * as ir from "./ir.ts"
import type { Binder, Expr, Obligation, Scalar } from "./ir.ts"
import { checksFor, FAST_HEADER, FULL_HEADER, prove, render, TooLarge, withFallback, type Check } from "./lean.ts"
import { Translator, type ArgShape, type Law, type LawInstance } from "./translate.ts"

export const MINIMUM_LEAN = [4, 36, 0] as const
const CACHE_VERSION = 1
const SEARCH_BUDGET = 60_000
const RUNTIME_BUDGET = 4_000

export interface RunOptions extends Config {
  /** Project directory. Default: the current directory. */
  cwd?: string
  /** Write the generated Lean source to this file. */
  emit?: string
}

export type Status = "proved" | "checked" | "sampled" | "failed"

export interface Finding {
  kind: "counterexample" | "unproved" | "vacuous" | "throws" | "mismatch" | "unsupported" | "invalid"
  message: string
  file: string
  line: number
  column: number
  /** Source text of the statement concerned. */
  text?: string
  /** The inputs that show the problem, by the name they have in the law. */
  inputs?: Record<string, string>
  /** Extra lines, such as the two sides of a failed equality or Lean's output. */
  detail?: string
}

export interface LawReport {
  name: string
  file: string
  line: number
  column: number
  status: Status
  findings: Finding[]
  notes: string[]
  obligations: number
  cases: number
}

export interface Report {
  ok: boolean
  laws: LawReport[]
  /** Problems that prevented checking, such as TypeScript errors. */
  errors: string[]
  counts: Record<Status, number>
  obligations: number
  cachedObligations: number
  cases: number
  durationMs: number
  /** Theorems the default automation could not close under the fast header. */
  retried: number
  /** Milliseconds spent in each phase. */
  timings: { typescript: number; prove: number; retry: number; crossCheck: number }
  /** True when nothing changed since the previous run and its result was reused. */
  replayed: boolean
  lean: string
}

interface Cache {
  version: number
  lean: Record<string, string>
  proved: string[]
  replay?: { signature: string; sources: string[]; report: Report }
}

/** A path as shown to the user: relative inside the project, absolute outside it. */
export function displayPath(cwd: string, file: string): string {
  const path = relative(cwd, file)
  return path === "" || path.startsWith("..") ? file : path
}

const hash = (text: string) => createHash("sha256").update(text).digest("hex").slice(0, 32)
const packageRoot = dirname(dirname(fileURLToPath(import.meta.url)))

async function loadConfig(cwd: string): Promise<{ config: Config; file: string | undefined }> {
  for (const name of ["pudding.config.ts", "pudding.config.mts", "pudding.config.js", "pudding.config.mjs"]) {
    const file = join(cwd, name)
    if (!existsSync(file)) continue
    const module = (await import(pathToFileURL(file).href)) as { default?: Config }
    return { config: module.default ?? {}, file }
  }
  return { config: {}, file: undefined }
}

export function locateLean(config: Config, cwd: string): string {
  const explicit = config.lean ?? process.env["PUDDING_LEAN"]
  if (explicit) return isAbsolute(explicit) ? explicit : resolve(cwd, explicit)
  for (const root of [cwd, packageRoot]) {
    const found = globSync(".toolchain/lean-*/bin/lean", { cwd: root }).sort().at(-1)
    if (found) return join(root, found)
  }
  const elan = join(homedir(), ".elan", "bin", "lean")
  return existsSync(elan) ? elan : "lean"
}

function leanVersion(lean: string, cache: Cache): string {
  let key = lean
  try {
    const stat = statSync(lean)
    key = `${lean}:${stat.mtimeMs}:${stat.size}`
  } catch {
    // Resolved through PATH; ask the binary every time.
  }
  let version = cache.lean[key]
  if (!version || key === lean) {
    try {
      version = execFileSync(lean, ["--version"], { encoding: "utf8" }).trim()
    } catch {
      throw new Error(`Lean was not found at \`${lean}\`. Run \`npx pudding install-lean\`, or set PUDDING_LEAN to a Lean ${MINIMUM_LEAN.join(".")} binary.`)
    }
    cache.lean = { [key]: version }
  }
  const match = /version (\d+)\.(\d+)\.(\d+)/.exec(version)
  const found = match ? match.slice(1, 4).map(Number) : [0, 0, 0]
  const tooOld = MINIMUM_LEAN.findIndex((part, i) => found[i]! !== part)
  if (tooOld >= 0 && found[tooOld]! < MINIMUM_LEAN[tooOld]!) {
    throw new Error(`Pudding needs Lean ${MINIMUM_LEAN.join(".")} or newer, but \`${lean}\` is ${found.join(".")}.`)
  }
  return version
}

function cachePath(cwd: string): string {
  return existsSync(join(cwd, "node_modules")) ? join(cwd, "node_modules", ".cache", "pudding", "cache.json") : join(cwd, ".pudding", "cache.json")
}

function loadCache(file: string): Cache {
  try {
    const cache = JSON.parse(readFileSync(file, "utf8")) as Cache
    if (cache.version === CACHE_VERSION) return cache
  } catch {
    // Missing or unreadable: start fresh.
  }
  return { version: CACHE_VERSION, lean: {}, proved: [] }
}

function stamp(file: string): string {
  try {
    const stat = statSync(file)
    return `${file}:${stat.mtimeMs}:${stat.size}`
  } catch {
    return `${file}:missing`
  }
}

/** Identifies everything a result depends on, so an unchanged project can reuse it. */
function signatureOf(parts: unknown, files: string[]): string {
  const own = dirname(fileURLToPath(import.meta.url))
  return hash(JSON.stringify([parts, files.map(stamp), readdirSync(own).map(name => stamp(join(own, name)))]))
}

// ------------------------------------------------------------------ search

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

interface Assignments {
  /** True when every possible input is visited. */
  exhaustive: boolean
  each(visit: (env: Map<string, Scalar>) => boolean | void): void
}

/** Inputs to try: every combination when the space is small enough, otherwise a sample. */
function assignments(binders: readonly Binder[], strings: readonly string[], budget: number): Assignments {
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
function stringPool(expressions: readonly Expr[]): string[] {
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

function findInput(binders: readonly Binder[], condition: Expr): { found: Map<string, Scalar> | undefined; exhaustive: boolean } {
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

function showInputs(binders: readonly Binder[], env: Map<string, Scalar>): Record<string, string> {
  const shown: Record<string, string> = {}
  for (const binder of binders) {
    const value = env.get(binder.name)
    if (value !== undefined) shown[binder.label] = ir.showScalar(value)
  }
  return shown
}

function showValue(e: Expr, env: Map<string, Scalar>): string {
  try {
    return ir.showScalar(ir.evaluate(e, env))
  } catch {
    return "(throws)"
  }
}

// ----------------------------------------------------------------- runtime

function buildArgument(shape: ArgShape, env: Map<string, Scalar>): unknown {
  switch (shape.k) {
    case "binder": return env.get(shape.name)
    case "const": return shape.value
    case "array": return shape.items.map(item => buildArgument(item, env))
    case "record": return Object.fromEntries(shape.fields.map(([key, field]) => [key, buildArgument(field, env)]))
  }
}

interface RuntimeLaw {
  name: string
  callback: (input: unknown) => void
}

async function loadRuntime(file: string): Promise<RuntimeLaw[] | string> {
  const key = Symbol.for("pudding.registry")
  const registry: RuntimeLaw[] = []
  const globals = globalThis as Record<symbol, unknown>
  globals[key] = registry
  try {
    await import(`${pathToFileURL(file).href}?pudding=${Date.now()}`)
    return registry
  } catch (error) {
    return error instanceof Error ? error.message.split("\n")[0]! : String(error)
  } finally {
    delete globals[key]
  }
}

function modelHolds(instance: LawInstance, env: Map<string, Scalar>): boolean {
  try {
    return instance.obligations.every(o => ir.evaluate(o.guard, env) !== true || ir.evaluate(o.claim, env) === true)
  } catch (error) {
    if (error instanceof ir.EvaluationError) return false
    throw error
  }
}

function runtimeHolds(law: RuntimeLaw, argument: unknown): boolean {
  try {
    law.callback(argument)
    return true
  } catch {
    return false
  }
}

// --------------------------------------------------------------------- run

interface Pending {
  law: Law
  instance: LawInstance
  obligation: Obligation
  checks: Check[]
}

function emptyReport(lean: string): Report {
  return {
    ok: false, laws: [], errors: [], counts: { proved: 0, checked: 0, sampled: 0, failed: 0 },
    obligations: 0, cachedObligations: 0, cases: 0, durationMs: 0, replayed: false, lean,
    retried: 0, timings: { typescript: 0, prove: 0, retry: 0, crossCheck: 0 },
  }
}

export async function run(options: RunOptions = {}): Promise<Report> {
  const started = performance.now()
  const cwd = resolve(options.cwd ?? process.cwd())
  const loaded = await loadConfig(cwd)
  const given = Object.fromEntries(Object.entries(options).filter(([, value]) => value !== undefined)) as RunOptions
  const config: RunOptions = { ...loaded.config, ...given }
  const lawFiles = globSync(config.include ?? ["**/*.law.ts"], {
    cwd, exclude: ["**/node_modules/**", "**/.toolchain/**", ...(config.exclude ?? [])],
  }).sort().map(file => resolve(cwd, file))
  const tsconfig = resolve(cwd, config.tsconfig ?? "tsconfig.json")
  const cacheFile = cachePath(cwd)
  const cache = config.cache === false ? loadCache("") : loadCache(cacheFile)
  const lean = locateLean(config, cwd)
  const version = leanVersion(lean, cache)
  const report = emptyReport(version)
  const finish = () => {
    report.durationMs = Math.round(performance.now() - started)
    return report
  }
  if (!lawFiles.length) {
    report.errors.push("no law files were found")
    return finish()
  }
  if (!existsSync(tsconfig)) {
    report.errors.push(`${displayPath(cwd, tsconfig)} was not found; Pudding reads law files through a TypeScript project`)
    return finish()
  }

  const identity = { cache: CACHE_VERSION, version, lawFiles, tsconfig: stamp(tsconfig), config: { ...config, emit: undefined, cwd: undefined } }
  if (config.cache !== false && !config.emit && cache.replay && cache.replay.signature === signatureOf(identity, cache.replay.sources)) {
    return { ...cache.replay.report, replayed: true, durationMs: Math.round(performance.now() - started) }
  }

  // Read and translate the laws.
  const reading = performance.now()
  const api = new API({ cwd })
  let laws: Law[] = []
  let sources: string[] = []
  try {
    const snapshot = api.updateSnapshot({ openProjects: [tsconfig] })
    const project = snapshot.getProject(tsconfig) ?? snapshot.getProjects()[0]
    if (!project) {
      report.errors.push(`${displayPath(cwd, tsconfig)} could not be opened as a TypeScript project`)
      return finish()
    }
    const { program, checker } = project
    const diagnose = (file: string) => {
      const source = program.getSourceFile(file)
      for (const diagnostic of [...program.getSyntacticDiagnostics(file), ...program.getSemanticDiagnostics(file)]) {
        if (diagnostic.category !== DiagnosticCategory.Error) continue
        const at = source?.getLineAndCharacterOfPosition(diagnostic.pos)
        report.errors.push(`${displayPath(cwd, file)}:${at ? `${at.line + 1}:${at.character + 1}` : "?"} TS${diagnostic.code}: ${diagnostic.text}`)
      }
    }
    const readable = lawFiles.filter(file => {
      if (program.getSourceFile(file)) return true
      report.errors.push(`${displayPath(cwd, file)} is not included by ${displayPath(cwd, tsconfig)}`)
      return false
    })
    readable.forEach(diagnose)
    if (report.errors.length) return finish()
    const translator = new Translator(program, checker)
    for (const file of readable) laws.push(...translator.translateFile(program.getSourceFile(file)!))
    for (const file of translator.reached) if (!readable.includes(file)) diagnose(file)
    if (report.errors.length) return finish()
    sources = program.getSourceFileNames().filter(name => isAbsolute(name) && !name.includes("/node_modules/") && existsSync(name))
  } finally {
    api.close()
    report.timings.typescript = Math.round(performance.now() - reading)
  }

  // Turn obligations into Lean theorems.
  const lawReports = new Map<Law, LawReport>()
  const pending: Pending[] = []
  for (const law of laws) {
    const entry: LawReport = {
      name: law.name, file: law.file, line: law.line, column: law.column, status: "proved", findings: [], notes: [], obligations: 0, cases: 0,
    }
    lawReports.set(law, entry)
    if (law.problem) continue
    try {
      const batch: Pending[] = []
      for (const instance of law.instances) {
        for (const obligation of instance.obligations) {
          batch.push({ law, instance, obligation, checks: checksFor(instance.binders, obligation.guard, obligation.claim, law.proof) })
        }
      }
      pending.push(...batch)
    } catch (error) {
      if (!(error instanceof TooLarge)) throw error
      law.problem = { kind: "unsupported", message: error.message, file: law.file, line: law.line, column: law.column }
    }
  }

  // Prove what the cache does not already hold.
  const proved = new Set(cache.proved)
  const keyOf = (statement: string) => hash(version + "\0" + statement)
  const statements = [...new Set(pending.flatMap(p => p.checks.map(c => c.statement)))]
  const outcomes = new Map<string, { ok: boolean; message: string }>()
  const fresh: string[] = []
  for (const statement of statements) {
    if (proved.has(keyOf(statement))) outcomes.set(statement, { ok: true, message: "" })
    else fresh.push(statement)
  }
  report.obligations = statements.length
  report.cachedObligations = statements.length - fresh.length
  if (config.emit) {
    mkdirSync(dirname(resolve(cwd, config.emit)), { recursive: true })
    writeFileSync(resolve(cwd, config.emit), render(FAST_HEADER, statements))
  }
  // Statements with the default tactic start under the fast header. Proofs the
  // author supplied may name any lemma, so they go straight to the full
  // library, at the same time.
  const quick = fresh.filter(statement => withFallback(statement) !== undefined)
  const authored = fresh.filter(statement => withFallback(statement) === undefined)
  const proving = performance.now()
  const [first, own] = await Promise.all([prove(lean, FAST_HEADER, quick), prove(lean, FULL_HEADER, authored)])
  quick.forEach((statement, i) => outcomes.set(statement, first[i]!))
  authored.forEach((statement, i) => outcomes.set(statement, own[i]!))
  report.timings.prove = Math.round(performance.now() - proving)
  // A rejection under the fast header is only final once the full library and
  // the slower fallback automation have also failed. Lean's first message is
  // kept because it describes the goal best.
  const retrying = performance.now()
  const retry = quick.filter((_, i) => !first[i]!.ok)
  const second = await prove(lean, FULL_HEADER, retry.map(statement => withFallback(statement)!))
  retry.forEach((statement, i) => {
    if (second[i]!.ok) outcomes.set(statement, second[i]!)
  })
  report.timings.retry = Math.round(performance.now() - retrying)
  report.retried = retry.length
  const used = new Set<string>()
  for (const statement of statements) if (outcomes.get(statement)!.ok) used.add(keyOf(statement))

  // Explain each obligation that Lean rejected.
  for (const { law, instance, obligation, checks } of pending) {
    const entry = lawReports.get(law)!
    entry.obligations += checks.length
    entry.cases += checks.reduce((n, c) => n + c.cases, 0)
    const rejected = checks.map(c => outcomes.get(c.statement)!).find(o => !o.ok)
    if (!rejected) continue
    const at = { file: obligation.file, line: obligation.line, column: obligation.column, text: obligation.text }
    const violated = ir.and(obligation.guard, ir.not(obligation.claim))
    const { found } = findInput(instance.binders, violated)
    if (found) {
      const inputs = showInputs(instance.binders, found)
      if (obligation.kind === "expect") {
        const sides = obligation.sides
        entry.findings.push({
          kind: "counterexample", message: "the expectation does not hold", ...at, inputs,
          ...(sides ? { detail: `actual:   ${showValue(sides.actual, found)}\nexpected: ${sides.negated ? "anything but " : ""}${showValue(sides.expected, found)}` } : {}),
        })
      } else {
        entry.findings.push({
          kind: "throws", ...at, inputs,
          message: obligation.kind === "nothrow" ? "this divides by zero"
            : obligation.kind === "falloff" ? "this function reaches its end without returning a value" : "this throw is reached",
        })
      }
    } else {
      const message = obligation.kind === "expect" ? "Lean could not prove this, and no counterexample was found"
        : obligation.kind === "nothrow" ? "Lean could not prove that the divisor is never zero"
        : obligation.kind === "falloff" ? "Lean could not prove that this function always returns a value"
        : "Lean could not prove that this throw is never reached"
      entry.findings.push({ kind: "unproved", message, ...at, detail: rejected.message.split("\n").slice(0, 8).join("\n") })
    }
  }

  // An expectation whose condition can never be true proves nothing.
  const vacuityChecks: { entry: LawReport; site: { line: number; column: number; text: string }; law: Law; checks: Check[] }[] = []
  for (const law of laws) {
    if (law.problem) continue
    const entry = lawReports.get(law)!
    for (const [key, site] of law.expectSites) {
      const reaching = law.instances.flatMap(instance => instance.obligations
        .filter(o => o.kind === "expect" && `${o.line}:${o.column}` === key).map(obligation => ({ instance, obligation })))
      const vacuous = () => entry.findings.push({
        kind: "vacuous", message: "this expectation is never reached, so it proves nothing", file: law.file, ...site,
      })
      if (!reaching.length) {
        vacuous()
        continue
      }
      const searches = reaching.map(({ instance, obligation }) => findInput(instance.binders, obligation.guard))
      if (searches.some(s => s.found)) continue
      if (searches.every(s => s.exhaustive)) vacuous()
      else {
        const checks = reaching.flatMap(({ instance, obligation }) => checksFor(instance.binders, obligation.guard, ir.FALSE, undefined))
        vacuityChecks.push({ entry, site, law, checks })
      }
    }
  }
  if (vacuityChecks.length) {
    const all = [...new Set(vacuityChecks.flatMap(v => v.checks.map(c => c.statement)))]
    const results = await prove(lean, FAST_HEADER, all)
    const neverTrue = new Set(all.filter((_, i) => results[i]!.ok))
    for (const { entry, site, law, checks } of vacuityChecks) {
      if (checks.every(c => neverTrue.has(c.statement))) {
        entry.findings.push({ kind: "vacuous", message: "the condition guarding this expectation is never true, so it proves nothing", file: law.file, ...site })
      } else entry.notes.push(`line ${site.line}: no input satisfying the condition was found by sampling`)
    }
  }

  // Run the real code and compare it with the model that was proved.
  const executedOnly = new Map<Law, boolean>()
  const executing = performance.now()
  if (config.crossCheck !== false) {
    for (const file of new Set(laws.map(law => law.file))) {
      const inFile = laws.filter(law => law.file === file && law.index >= 0)
      const runtime = await loadRuntime(file)
      const reason = typeof runtime === "string" ? `the law file could not be executed (${runtime})`
        : runtime.length !== inFile.length ? "the law file registered a different number of laws when executed" : undefined
      for (const law of inFile) {
        const entry = lawReports.get(law)!
        if (law.problem?.kind === "invalid") continue
        if (reason || typeof runtime === "string") {
          entry.notes.push(`not compared with the running code: ${reason}`)
          continue
        }
        const real = runtime[law.index]!
        let exhaustive = true
        let executed = 0
        for (const instance of law.instances) {
          const space = assignments(instance.binders, stringPool(instance.obligations.flatMap(o => [o.guard, o.claim])), RUNTIME_BUDGET)
          exhaustive &&= space.exhaustive
          space.each(env => {
            executed++
            const actual = runtimeHolds(real, instance.arg ? buildArgument(instance.arg, env) : undefined)
            if (law.problem) {
              if (actual) return false
              entry.findings.push({
                kind: "counterexample", message: "the law fails when executed", file: law.file, line: law.line, column: law.column,
                inputs: showInputs(instance.binders, env),
              })
              return true
            }
            const expected = modelHolds(instance, env)
            if (actual === expected) return false
            entry.findings.push({
              kind: "mismatch", file: law.file, line: law.line, column: law.column, inputs: showInputs(instance.binders, env),
              message: `the running code ${actual ? "satisfies" : "violates"} the law for this input, but the model Pudding proved things about ${expected ? "satisfies" : "violates"} it; the proof cannot be trusted`,
            })
            return true
          })
        }
        if (law.problem && executed) executedOnly.set(law, exhaustive)
      }
    }
  }

  report.timings.crossCheck = Math.round(performance.now() - executing)

  // Settle each law's status.
  for (const law of laws) {
    const entry = lawReports.get(law)!
    if (law.problem) {
      const { kind, message, file, line, column } = law.problem
      if (kind === "invalid") entry.findings.push({ kind, message, file, line, column })
      else if (!executedOnly.has(law)) {
        entry.findings.push({ kind, message: `${message}; the law could not be executed instead, so nothing was checked`, file, line, column })
      } else {
        entry.status = executedOnly.get(law) ? "checked" : "sampled"
        entry.notes.unshift(`not proved: ${message} (${displayPath(cwd, file)}:${line}:${column})`)
      }
    }
    if (entry.findings.length) entry.status = "failed"
    if (config.strict && entry.status !== "proved" && entry.status !== "failed") {
      entry.status = "failed"
      entry.findings.push({ kind: "unsupported", message: "strict mode requires a proof, and this law was only executed", file: law.file, line: law.line, column: law.column })
    }
    report.counts[entry.status]++
    report.cases += entry.cases
    report.laws.push(entry)
  }
  report.ok = report.counts.failed === 0 && report.errors.length === 0
  finish()

  if (config.cache !== false) {
    const saved: Cache = { version: CACHE_VERSION, lean: cache.lean, proved: [...used] }
    if (!config.emit) {
      const files = [...new Set([...sources, tsconfig, ...(loaded.file ? [loaded.file] : []), join(cwd, "package.json")])]
      saved.replay = { signature: signatureOf(identity, files), sources: files, report }
    }
    mkdirSync(dirname(cacheFile), { recursive: true })
    writeFileSync(cacheFile, JSON.stringify(saved, (_, value: unknown) => (typeof value === "bigint" ? value.toString() : value)))
  }
  return report
}
