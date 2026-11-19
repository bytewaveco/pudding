// Orchestrates a run: read the laws with the TypeScript compiler, prove the
// resulting obligations in Lean, explain what failed, and compare the proved
// model with the real code.

import { execFileSync } from "node:child_process"
import { createHash } from "node:crypto"
import { existsSync, globSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs"
import { homedir } from "node:os"
import { dirname, isAbsolute, join, relative, resolve } from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"
import { Worker } from "node:worker_threads"
import { SyntaxKind as K } from "typescript/unstable/ast"
import { API, DiagnosticCategory, SymbolFlags, type Checker, type Program } from "typescript/unstable/sync"
import type { Config } from "./index.ts"
import * as ir from "./ir.ts"
import type { Obligation } from "./ir.ts"
import type { FileOutcome, Job, RuntimeMap } from "./crosscheck.ts"
import { findInput, showInputs, showValue } from "./search.ts"
import { checksFor, FAST_HEADER, FULL_HEADER, prove, render, TooLarge, withFallback, type Check } from "./lean.ts"
import { Translator, type Law, type LawInstance } from "./translate.ts"

export const MINIMUM_LEAN = [4, 36, 0] as const
const CACHE_VERSION = 1
const RUNTIME_BUDGET = 4_000
const RUNTIME_TIMEOUT_MS = 30_000

export interface RunOptions extends Config {
  /** Project directory. Default: the current directory. */
  cwd?: string
  /** Only check law files whose path contains one of these. */
  files?: string[]
  /** Only check laws whose full name matches this regular expression. */
  name?: string
  /** Write the generated Lean source to this file. */
  emit?: string
}

export type Status = "proved" | "checked" | "sampled" | "failed" | "skipped" | "todo"

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
  /** Things that weakened the run without failing it, such as a law file that could not be executed. */
  warnings: string[]
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
  /** The reporter the project's configuration asks for, if any. */
  reporter?: Config["reporter"]
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

const packageRoot = dirname(dirname(fileURLToPath(import.meta.url)))
/** The name law files import from, read from this package so a rename needs no code change. */
export const packageName = (JSON.parse(readFileSync(join(packageRoot, "package.json"), "utf8")) as { name: string }).name

const hash = (text: string) => createHash("sha256").update(text).digest("hex").slice(0, 32)
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

/**
 * Write the TypeScript project Pudding reads the laws through: the law files
 * as roots, on top of the project's own compiler options. This is why law
 * files need no entry in anyone's `include`, and why a project without a
 * tsconfig still works.
 */
function writeProject(directory: string, base: string | undefined, lawFiles: string[]): string {
  const defaults = join(directory, "tsconfig.defaults.json")
  const project = join(directory, "tsconfig.json")
  const write = (file: string, value: unknown) => {
    const text = JSON.stringify(value, null, 2) + "\n"
    if (!existsSync(file) || readFileSync(file, "utf8") !== text) writeFileSync(file, text)
  }
  mkdirSync(directory, { recursive: true })
  write(defaults, {
    compilerOptions: { target: "ESNext", module: "Preserve", moduleResolution: "Bundler", strict: true, skipLibCheck: true },
  })
  write(project, {
    extends: base ? [defaults, base] : [defaults],
    compilerOptions: { noEmit: true, allowImportingTsExtensions: true, composite: false, incremental: false, declaration: false },
    files: lawFiles,
    include: [],
    exclude: [],
  })
  return project
}

// ----------------------------------------------------------------- runtime

/**
 * What Node needs to execute the law files the way TypeScript reads them:
 * where each import resolves, and which imported or exported names are types
 * only. Node erases type syntax but neither resolves `./cart` to `./cart.ts`
 * nor drops an imported interface, and bundler-style code relies on both.
 */
function runtimeMap(program: Program, checker: Checker): RuntimeMap {
  const map: RuntimeMap = { resolutions: new Map(), elided: new Map() }
  // The compiler's nodes are handled untyped, as in the translator.
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  type N = any
  for (const name of program.getSourceFileNames()) {
    if (!isAbsolute(name) || name.includes("/node_modules/")) continue
    const source = program.getSourceFile(name)
    if (!source || source.isDeclarationFile) continue
    const text = source.text
    const resolutions = new Map<string, string>()
    const ranges: [number, number][] = []
    /** The range of a binding, widened over one neighbouring comma. */
    const withComma = (node: N): [number, number] => {
      let start = node.getStart(source) as number
      let end = node.end as number
      const after = /^\s*,/.exec(text.slice(end))
      if (after) end += after[0].length
      else {
        const before = /,\s*$/.exec(text.slice(0, start))
        if (before) start -= before[0].length
      }
      return [start, end]
    }
    for (const statement of source.statements as readonly N[]) {
      const isImport = statement.kind === K.ImportDeclaration
      if (!isImport && statement.kind !== K.ExportDeclaration) continue
      const specifier = statement.moduleSpecifier
      if (specifier?.kind === K.StringLiteral) {
        const symbol = checker.getSymbolAtLocation(specifier)
        const target = (symbol?.valueDeclaration ?? symbol?.declarations[0])?.resolve()?.getSourceFile()
        if (target && !target.isDeclarationFile && !program.isSourceFileFromExternalLibrary(target)) resolutions.set(specifier.text, target.fileName)
      }
      if (isImport ? statement.importClause?.phaseModifier === K.TypeKeyword : statement.isTypeOnly) continue
      const bindings: N[] = isImport
        ? statement.importClause?.namedBindings?.kind === K.NamedImports ? [...statement.importClause.namedBindings.elements] : []
        : statement.exportClause?.kind === K.NamedExports ? [...statement.exportClause.elements] : []
      const typeOnly = bindings.filter(binding => {
        if (binding.isTypeOnly) return false
        let symbol = checker.getSymbolAtLocation(binding.name)
        if (symbol && symbol.flags & SymbolFlags.Alias) symbol = checker.getAliasedSymbol(symbol)
        return !!symbol && !checker.isUnknownSymbol(symbol) && (symbol.flags & SymbolFlags.Value) === 0
      })
      // TypeScript drops an import whose names are all types; so must we, or Node would load a module for nothing.
      const whole = isImport && typeOnly.length > 0 && typeOnly.length === bindings.length && !statement.importClause.name
      if (whole) ranges.push([statement.getStart(source), statement.end])
      else for (const binding of typeOnly) ranges.push(withComma(binding))
    }
    if (resolutions.size) map.resolutions.set(name, resolutions)
    if (ranges.length) map.elided.set(name, ranges)
  }
  return map
}

/**
 * Execute the laws in a worker thread: fresh module state on every run, no
 * way for the project's code to disturb this process, and a time limit.
 */
function executeLaws(job: Job): Promise<{ outcomes: Map<string, FileOutcome>; timedOut: boolean }> {
  return new Promise(resolve => {
    const outcomes = new Map<string, FileOutcome>()
    const entry = new URL(import.meta.url.replace(/runner\.(ts|js)$/, "crosscheck.$1"))
    const worker = new Worker(entry, { workerData: job, stdout: true, stderr: true })
    let settled = false
    const finish = (timedOut: boolean) => {
      if (settled) return
      settled = true
      clearTimeout(timer)
      void worker.terminate()
      resolve({ outcomes, timedOut })
    }
    const timer = setTimeout(() => finish(true), RUNTIME_TIMEOUT_MS)
    worker.on("message", (message: FileOutcome | "done") => {
      if (message === "done") finish(false)
      else outcomes.set(message.file, message)
    })
    worker.on("error", () => finish(false))
    worker.on("exit", () => finish(false))
  })
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
    ok: false, laws: [], errors: [], warnings: [], counts: { proved: 0, checked: 0, sampled: 0, failed: 0, skipped: 0, todo: 0 },
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
  const filters = config.files ?? []
  const lawFiles = globSync(config.include ?? ["**/*.law.ts"], {
    cwd, exclude: ["**/node_modules/**", "**/.toolchain/**", ...(config.exclude ?? [])],
  }).sort().map(file => resolve(cwd, file)).filter(file => !filters.length || filters.some(filter => displayPath(cwd, file).includes(filter)))
  const base = resolve(cwd, config.tsconfig ?? "tsconfig.json")
  const cacheFile = cachePath(cwd)
  const cache = config.cache === false ? loadCache("") : loadCache(cacheFile)
  const lean = locateLean(config, cwd)
  const version = leanVersion(lean, cache)
  const report = emptyReport(version)
  if (config.reporter) report.reporter = config.reporter
  const finish = () => {
    report.durationMs = Math.round(performance.now() - started)
    return report
  }
  if (!lawFiles.length) {
    report.errors.push(filters.length ? `no law file matches ${filters.map(f => `\`${f}\``).join(" or ")}` : "no law files were found")
    return finish()
  }
  if (config.tsconfig && !existsSync(base)) {
    report.errors.push(`the tsconfig \`${config.tsconfig}\` named in the configuration was not found`)
    return finish()
  }
  let selected: (name: string) => boolean = () => true
  if (config.name) {
    try {
      const pattern = new RegExp(config.name)
      selected = name => pattern.test(name)
    } catch {
      report.errors.push(`\`${config.name}\` is not a valid regular expression`)
      return finish()
    }
  }

  const identity = { cache: CACHE_VERSION, version, lawFiles, tsconfig: stamp(base), config: { ...config, emit: undefined, cwd: undefined, reporter: undefined } }
  if (config.cache !== false && !config.emit && cache.replay && cache.replay.signature === signatureOf(identity, cache.replay.sources)) {
    return { ...cache.replay.report, replayed: true, durationMs: Math.round(performance.now() - started) }
  }
  const tsconfig = writeProject(dirname(cacheFile), existsSync(base) ? base : undefined, lawFiles)

  // Read and translate the laws.
  const reading = performance.now()
  const api = new API({ cwd })
  let laws: Law[] = []
  let sources: string[] = []
  let executable: RuntimeMap | undefined
  try {
    const snapshot = api.updateSnapshot({ openProjects: [tsconfig] })
    const project = snapshot.getProject(tsconfig) ?? snapshot.getProjects()[0]
    if (!project) {
      report.errors.push("TypeScript could not open the project Pudding generated for the law files")
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
      report.errors.push(`${displayPath(cwd, file)} could not be read by TypeScript`)
      return false
    })
    readable.forEach(diagnose)
    if (report.errors.length) return finish()
    const translator = new Translator(program, checker, packageName)
    for (const file of readable) laws.push(...translator.translateFile(program.getSourceFile(file)!, selected))
    for (const file of translator.reached) if (!readable.includes(file)) diagnose(file)
    if (report.errors.length) return finish()
    sources = program.getSourceFileNames().filter(name => isAbsolute(name) && !name.includes("/node_modules/") && existsSync(name))
    if (config.crossCheck !== false) executable = runtimeMap(program, checker)
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
    if (law.problem || law.mode !== "run") continue
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
    if (law.problem || law.mode !== "run") continue
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
  if (executable) {
    const candidates = laws.filter(law => law.index >= 0)
    const job: Job = {
      map: executable,
      budget: RUNTIME_BUDGET,
      files: [...new Set(candidates.map(law => law.file))].map(file => ({
        file,
        registered: candidates.filter(law => law.file === file).length,
        laws: candidates.filter(law => law.file === file && law.mode === "run" && law.problem?.kind !== "invalid").map(law => ({
          index: law.index,
          unproved: law.problem !== undefined,
          instances: law.instances.map(instance => ({
            binders: instance.binders, arg: instance.arg, obligations: instance.obligations.map(o => ({ guard: o.guard, claim: o.claim })),
          })),
        })),
      })),
    }
    const { outcomes, timedOut } = await executeLaws(job)
    for (const { file } of job.files) {
      const outcome = outcomes.get(file)
      const reason = outcome?.error ?? (outcome ? undefined : timedOut ? `executing the laws took longer than ${RUNTIME_TIMEOUT_MS / 1000} s` : "the worker that executes laws stopped unexpectedly")
      if (reason) report.warnings.push(`${displayPath(cwd, file)} was not compared with the running code: ${reason}`)
      for (const result of outcome?.laws ?? []) {
        const law = candidates.find(candidate => candidate.file === file && candidate.index === result.index)!
        const entry = lawReports.get(law)!
        if (result.failure) {
          const { kind, inputs, actual, expected } = result.failure
          entry.findings.push({
            kind, inputs, file: law.file, line: law.line, column: law.column,
            message: kind === "counterexample" ? "the law fails when executed"
              : `the running code ${actual ? "satisfies" : "violates"} the law for this input, but the model Pudding proved things about ${expected ? "satisfies" : "violates"} it; the proof cannot be trusted`,
          })
        }
        if (law.problem && result.executed) executedOnly.set(law, result.exhaustive)
      }
    }
  }

  report.timings.crossCheck = Math.round(performance.now() - executing)

  // Settle each law's status.
  for (const law of laws) {
    const entry = lawReports.get(law)!
    if (law.mode !== "run") entry.status = law.mode === "todo" ? "todo" : "skipped"
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
    if (config.strict && (entry.status === "checked" || entry.status === "sampled")) {
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
      const files = [...new Set([...sources, base, ...(loaded.file ? [loaded.file] : []), join(cwd, "package.json")])]
      saved.replay = { signature: signatureOf(identity, files), sources: files, report }
    }
    mkdirSync(dirname(cacheFile), { recursive: true })
    writeFileSync(cacheFile, JSON.stringify(saved, (_, value: unknown) => (typeof value === "bigint" ? value.toString() : value)))
  }
  return report
}
