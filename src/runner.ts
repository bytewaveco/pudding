// Orchestrates a run: read the laws with the TypeScript compiler, prove the
// resulting obligations in Lean, explain what failed, and compare the proved
// model with the real code.

import { execFileSync } from "node:child_process"
import { createHash } from "node:crypto"
import { createRequire } from "node:module"
import { appendFileSync, existsSync, globSync, mkdirSync, readdirSync, readFileSync, renameSync, statSync, writeFileSync } from "node:fs"
import { homedir } from "node:os"
import { dirname, isAbsolute, join, relative, resolve } from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"
import { threadId, Worker } from "node:worker_threads"
import { API, compiler, compilerProblem, DiagnosticCategory, ensureCompiler, SymbolFlags, SyntaxKind as K, type Checker, type Program } from "./compiler.ts"
import type { Config } from "./index.ts"
import { cacheDirectory, toolchainName } from "./install.ts"
import * as ir from "./ir.ts"
import type { Obligation } from "./ir.ts"
import type { FileOutcome, Job, RuntimeMap } from "./crosscheck.ts"
import { findInput, showInputs, showValue } from "./search.ts"
import { checksFor, FALLBACK_HEADER, FAST_HEADER, FULL_HEADER, proofKind, prove, render, scriptProblem, TooLarge, withFallback, type Check } from "./lean.ts"
import { Translator, type Law, type LawInstance } from "./translate.ts"

export const MINIMUM_LEAN = [4, 36, 0] as const
const CACHE_VERSION = 3
const PROVED_RUNTIME_BUDGET = 1_000
const FALLBACK_RUNTIME_BUDGET = 4_000
const RUNTIME_TIMEOUT_MS = 30_000

/** Dependency-tracking session for watch mode so edits re-check only affected law files. */
export interface WatchSession {
  /** Clear tracked dependency state. */
  close(): void
  /** Law files affected by a change to `changedFile`, or `undefined` when a full run is needed. */
  affected(changedFile: string): string[] | undefined
  /** Internal dependency graph mapping each law file to every file it transitively imports or reaches. */
  readonly _internal: { dependencies: Map<string, Set<string>> }
}

export function createWatchSession(): WatchSession {
  const state: WatchSession["_internal"] = { dependencies: new Map() }
  return {
    _internal: state,
    close() {
      state.dependencies.clear()
    },
    affected(changedFile: string) {
      if (!state.dependencies.size) return undefined
      const target = resolve(changedFile)
      const hit: string[] = []
      for (const [lawFile, reached] of state.dependencies) {
        if (lawFile === target || reached.has(target)) hit.push(lawFile)
      }
      return hit
    },
  }
}

/** Collect every project file transitively imported or re-exported by `entry`, including type-only imports and `.d.ts` files. */
function collectDependencies(program: Program, checker: Checker, entry: string): Set<string> {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  type N = any
  const visited = new Set<string>([resolve(entry)])
  const queue = [entry]
  while (queue.length) {
    const current = queue.pop()!
    const source = program.getSourceFile(current)
    if (!source) continue
    const addFile = (fileName: string) => {
      const full = resolve(fileName)
      if (visited.has(full)) return
      const target = program.getSourceFile(fileName) ?? program.getSourceFile(full)
      if (target && (program.isSourceFileFromExternalLibrary(target) || program.isSourceFileDefaultLibrary(target))) return
      visited.add(full)
      queue.push(target ? target.fileName : full)
    }
    const addSpecifier = (specifier: N) => {
      if (!specifier || specifier.kind !== K.StringLiteral) return
      const symbol = checker.getSymbolAtLocation(specifier)
      const target = (symbol?.valueDeclaration ?? symbol?.declarations[0])?.resolve()?.getSourceFile()
      if (!target || program.isSourceFileFromExternalLibrary(target) || program.isSourceFileDefaultLibrary(target)) return
      addFile(target.fileName)
    }
    const visit = (node: N) => {
      if ((node.kind === K.ImportDeclaration || node.kind === K.ExportDeclaration) && node.moduleSpecifier) {
        addSpecifier(node.moduleSpecifier)
      } else if (K.ImportType !== undefined && node.kind === K.ImportType && node.argument?.kind === K.LiteralType && node.argument.literal?.kind === K.StringLiteral) {
        addSpecifier(node.argument.literal)
      }
      node.forEachChild(visit)
    }
    visit(source)
    // Also track triple-slash `/// <reference path="..." />` directives (e.g. local `.d.ts` files).
    const referenced = (source as { referencedFiles?: readonly { fileName: string }[] }).referencedFiles
    if (referenced) {
      for (const ref of referenced) {
        const target = resolve(dirname(current), ref.fileName)
        if (existsSync(target) || program.getSourceFile(target)) addFile(target)
      }
    }
    for (const match of source.text.matchAll(/^[ \t]*\/\/\/[ \t]*<reference[ \t]+path[ \t]*=[ \t]*["']([^"']+)["']/gm)) {
      const target = resolve(dirname(current), match[1]!)
      if (existsSync(target) || program.getSourceFile(target)) addFile(target)
    }
  }
  return visited
}

export interface RunOptions extends Config {
  /** Project directory. Default: the current directory. */
  cwd?: string
  /** Only check law files whose path contains one of these. */
  files?: string[]
  /** Check exactly these files, whatever the configuration includes. */
  lawFiles?: string[]
  /** Only check laws whose full name matches this regular expression. */
  name?: string
  /** Write the generated Lean source to this file. */
  emit?: string
  /** Optional persistent watch session that reuses the TypeScript 7 compiler API across edits. */
  session?: WatchSession
}

export type Status = "proved" | "checked" | "sampled" | "failed" | "skipped" | "todo"

export interface Finding {
  kind: "counterexample" | "unproved" | "vacuous" | "throws" | "inexact" | "mismatch" | "unsupported" | "invalid"
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
  /** The reporter the project's configuration asks for, if any. */
  reporter?: Config["reporter"]
  lean: string
  /** The compiler that read the project, such as `TypeScript 7.0.2`. */
  compiler: string
}

/**
 * What a project remembers between runs: which Lean binary is which version.
 * The theorems Lean has accepted are remembered for the whole machine, in
 * the proof log.
 */
interface Cache {
  version: number
  lean: Record<string, string>
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
    // The query makes a changed file load again when one process runs several times, as watch mode does.
    const module = (await import(`${pathToFileURL(file).href}?changed=${statSync(file).mtimeMs}`)) as { default?: Config }
    return { config: module.default ?? {}, file }
  }
  return { config: {}, file: undefined }
}

/** Raised when no Lean binary can be found, so the CLI can offer to install one. */
export class LeanMissing extends Error {}

/**
 * Find the Lean binary. In order: the configuration, `PUDDING_LEAN`, the
 * runtime package for this platform, a `.toolchain` directory in the project
 * or in this package, the machine-wide cache `install-lean` fills, elan, and
 * finally `lean` on the PATH.
 */
export function locateLean(config: Config, cwd: string): string {
  const explicit = config.lean ?? process.env["PUDDING_LEAN"]
  if (explicit) return isAbsolute(explicit) ? explicit : resolve(cwd, explicit)
  const suffix = process.platform === "win32" ? ".exe" : ""
  const name = toolchainName()
  // What `install-lean` left behind: in the project, next to Pudding itself, or in the shared cache.
  const installed = [
    ...[cwd, packageRoot].flatMap(root => globSync(".toolchain/lean-*/bin/lean" + suffix, { cwd: root }).sort().slice(-1).map(found => join(root, found))),
    ...(name ? [join(cacheDirectory(), name, "bin", "lean" + suffix)] : []),
  ].filter(candidate => existsSync(candidate))
  // A whole Lean is only there because someone asked for one, so that a proof
  // of their own can use more of the library. It goes before the trimmed
  // runtime package for that reason.
  const whole = installed.find(candidate => existsSync(join(dirname(dirname(candidate)), "lib", "lean", "Lean.olean")))
  if (whole) return whole
  try {
    const manifest = createRequire(import.meta.url).resolve(`${packageName}-lean-${process.platform}-${process.arch}/package.json`)
    const bundled = join(dirname(manifest), "bin", "lean" + suffix)
    if (existsSync(bundled)) return bundled
  } catch {
    // The runtime package is optional.
  }
  const elan = join(homedir(), ".elan", "bin", "lean" + suffix)
  return installed[0] ?? (existsSync(elan) ? elan : "lean")
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
      throw new LeanMissing(lean === "lean"
        ? `Lean is not installed. Run \`npx pudding install-lean\`, or set PUDDING_LEAN to a Lean ${MINIMUM_LEAN.join(".")} binary.`
        : `Lean could not be run at \`${lean}\`. Run \`npx pudding install-lean\`, or set PUDDING_LEAN to a Lean ${MINIMUM_LEAN.join(".")} binary.`)
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

/** The most proofs the log keeps when it is rewritten. It is rewritten when it holds twice as many. */
const CACHE_LIMIT = 50_000

function cachePath(cwd: string): string {
  return existsSync(join(cwd, "node_modules")) ? join(cwd, "node_modules", ".cache", "pudding", "cache.json") : join(cwd, ".pudding", "cache.json")
}

/** Write a file so that another run reading it at the same moment never sees half of it. */
function replaceFile(file: string, text: string): void {
  const partial = `${file}.${process.pid}.${threadId}.tmp`
  writeFileSync(partial, text)
  renameSync(partial, file)
}

function loadCache(file: string): Cache {
  try {
    const cache = JSON.parse(readFileSync(file, "utf8")) as Cache
    if (cache.version === CACHE_VERSION) return cache
  } catch {
    // Missing or unreadable: start fresh.
  }
  return { version: CACHE_VERSION, lean: {} }
}

/**
 * The theorems Lean has accepted, shared by every project on the machine, so
 * that a new worktree or a second project does not prove them again. Each
 * line is a key made from a theorem's full text, the Lean version and this
 * build of Pudding, so reusing one cannot be wrong: a build that judges Lean's
 * answers differently, released or not, never trusts another build's keys.
 * Whole results are deliberately not reused: knowing that nothing relevant
 * changed would mean second-guessing TypeScript's module resolution. Runs
 * append to the log, so runs going at once, as Vitest's workers do, keep each
 * other's proofs. Only rewriting a log grown to twice its limit can drop a
 * proof, which then costs time again.
 */
const proofLog = () => join(cacheDirectory(), "proved")
const KEY = /^[0-9a-f]{32}$/

/** A digest of the code running now: every module next to this one. */
function buildDigest(): string {
  const directory = dirname(fileURLToPath(import.meta.url))
  const digest = createHash("sha256")
  for (const file of readdirSync(directory).sort()) {
    if (/\.(js|ts)$/.test(file) && !file.endsWith(".d.ts")) digest.update(file + "\0").update(readFileSync(join(directory, file)))
  }
  return digest.digest("hex")
}

function loadProofs(): { keys: Set<string>; lines: number } {
  try {
    const lines = readFileSync(proofLog(), "utf8").split("\n")
    return { keys: new Set(lines.filter(line => KEY.test(line))), lines: lines.length }
  } catch {
    return { keys: new Set(), lines: 0 }
  }
}

/** A cache that cannot be written only costs time, so a failure here is ignored. */
function saveProofs(known: { keys: Set<string>; lines: number }, added: string[]): void {
  if (!added.length) return
  try {
    mkdirSync(dirname(proofLog()), { recursive: true })
    if (known.lines + added.length > 2 * CACHE_LIMIT) replaceFile(proofLog(), [...known.keys, ...added].slice(-CACHE_LIMIT).join("\n") + "\n")
    else appendFileSync(proofLog(), added.map(key => key + "\n").join(""))
  } catch {
    // Read-only or missing cache directory.
  }
}

/**
 * Write the TypeScript project Pudding reads the laws through: the law files
 * as roots, on top of the project's own compiler options. This is why law
 * files need no entry in anyone's `include`, and why a project without a
 * tsconfig still works.
 */
function writeProject(directory: string, base: string | undefined, lawFiles: string[], partial: boolean): string {
  const defaults = join(directory, "tsconfig.defaults.json")
  // A run over some of the law files gets a project of its own, because
  // several of them can be going at once: Vitest proves each file in its own worker.
  const subset = createHash("sha256").update(lawFiles.join("\0")).digest("hex").slice(0, 12)
  const project = join(directory, partial ? `tsconfig.${subset}.json` : "tsconfig.json")
  const write = (file: string, value: unknown) => {
    const text = JSON.stringify(value, null, 2) + "\n"
    if (!existsSync(file) || readFileSync(file, "utf8") !== text) replaceFile(file, text)
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
function runtimeMap(program: Program, checker: Checker, ambiguous: (message: string) => void): RuntimeMap {
  const map: RuntimeMap = { resolutions: new Map(), elided: new Map() }
  // The compiler's nodes are handled untyped, as in the translator.
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  type N = any
  for (const name of program.getSourceFileNames()) {
    if (!isAbsolute(name) || name.replaceAll("\\", "/").includes("/node_modules/")) continue
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
        if (target && !target.isDeclarationFile && !program.isSourceFileFromExternalLibrary(target)) {
          // `./x.js` normally means the TypeScript file `./x.ts`. If a real
          // `./x.js` also exists, Node runs that one, and it may not be what
          // TypeScript read. Leave the import to Node and say so.
          const literal = /^\.{1,2}\//.test(specifier.text) ? resolve(dirname(name), specifier.text) : undefined
          if (literal && literal !== target.fileName && existsSync(literal) && statSync(literal).isFile()) {
            ambiguous(`${name} imports \`${specifier.text}\`, and both that file and ${target.fileName} exist: TypeScript reads one and Node runs the other, so a proof about the first says nothing certain about the second. Remove one of them or import the TypeScript file by its own name`)
          } else resolutions.set(specifier.text, target.fileName)
        }
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
    obligations: 0, cachedObligations: 0, cases: 0, durationMs: 0, lean, compiler,
    retried: 0, timings: { typescript: 0, prove: 0, retry: 0, crossCheck: 0 },
  }
}

export async function run(options: RunOptions = {}): Promise<Report> {
  const started = performance.now()
  const cwd = resolve(options.cwd ?? process.cwd())
  await ensureCompiler(cwd)
  const loaded = await loadConfig(cwd)
  const given = Object.fromEntries(Object.entries(options).filter(([, value]) => value !== undefined)) as RunOptions
  const config: RunOptions = { ...loaded.config, ...given }
  const filters = config.files ?? []
  const lawFiles = config.lawFiles?.map(file => resolve(cwd, file)) ?? globSync(config.include ?? ["**/*.law.ts"], {
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
  if (compilerProblem) {
    report.errors.push(compilerProblem)
    return finish()
  }
  if (!lawFiles.length) {
    if (options.session && config.lawFiles === undefined && !filters.length && !config.name) options.session._internal.dependencies.clear()
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

  const partial = config.lawFiles !== undefined || filters.length > 0 || config.name !== undefined
  const tsconfig = writeProject(dirname(cacheFile), existsSync(base) ? base : undefined, lawFiles, partial)

  // Read and translate the laws.
  const reading = performance.now()
  const session = options.session?._internal
  const api = new API({ cwd })
  let laws: Law[] = []
  let executable: RuntimeMap | undefined
  try {
    // TypeScript 7.1 and tsrs open projects with `createSnapshot`; 7.0 uses `updateSnapshot`.
    const open = { openProjects: [tsconfig] }
    const snapshot = "createSnapshot" in api && typeof api.createSnapshot === "function"
      ? api.createSnapshot(open)
      : api.updateSnapshot(open)
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
    if (report.errors.length) {
      session?.dependencies.clear()
      return finish()
    }
    const translator = new Translator(program, checker, packageName)
    if (session && !partial) session.dependencies.clear()
    for (const file of readable) {
      laws.push(...translator.translateFile(program.getSourceFile(file)!, selected))
      if (session) {
        const deps = collectDependencies(program, checker, file)
        for (const reached of translator.fileReached.get(file) ?? []) deps.add(resolve(reached))
        session.dependencies.set(resolve(file), deps)
      }
    }
    for (const file of translator.reached) if (!readable.includes(file)) diagnose(file)
    if (report.errors.length) {
      session?.dependencies.clear()
      return finish()
    }
    const map = runtimeMap(program, checker, message => report.errors.push(message.replaceAll(cwd + "/", "").replaceAll(cwd + "\\", "")))
    if (report.errors.length) {
      session?.dependencies.clear()
      return finish()
    }
    if (config.crossCheck !== false) executable = map
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
    const unusable = law.proof === undefined ? undefined : scriptProblem(law.proof)
    if (unusable) {
      law.problem = { kind: "invalid", message: unusable, file: law.file, line: law.line, column: law.column }
      continue
    }
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
      for (const instance of law.instances) instance.obligations = []
    }
  }

  // Start executing the laws against the real code now; it runs alongside
  // the proving and is compared with the model once both are done.
  const executing = performance.now()
  const candidates = laws.filter(law => law.index >= 0)
  const job: Job | undefined = executable && {
    map: executable,
    budget: FALLBACK_RUNTIME_BUDGET,
    files: lawFiles.map(file => ({
      file,
      registered: candidates.filter(law => law.file === file).length,
      laws: candidates.filter(law => law.file === file && law.mode === "run" && law.problem?.kind !== "invalid").map(law => ({
        index: law.index,
        unproved: law.problem !== undefined,
        budget: law.problem ? FALLBACK_RUNTIME_BUDGET : PROVED_RUNTIME_BUDGET,
        mentioned: law.mentioned,
        instances: law.instances.map(instance => ({
          binders: instance.binders, arg: instance.arg, obligations: instance.obligations.map(o => ({ guard: o.guard, claim: o.claim, inexact: o.kind === "overflow" || o.kind === "nan" || o.kind === "round" || o.kind === "inherited" })),
        })),
      })),
    })),
  }
  const execution = job && executeLaws(job).then(result => {
    report.timings.crossCheck = Math.round(performance.now() - executing)
    return result
  })

  // Prove what the cache does not already hold.
  const known = config.cache === false ? { keys: new Set<string>(), lines: 0 } : loadProofs()
  const proved = known.keys
  const build = buildDigest()
  const keyOf = (statement: string) => hash(build + "\0" + version + "\0" + statement)
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
    const comments = new Map<string, string>()
    for (const { law, instance, obligation, checks } of pending) {
      const mapping = instance.binders.filter(b => b.label !== b.name).map(b => `${b.name} = ${b.label}`).join(", ")
      const note = `${displayPath(cwd, obligation.file)}:${obligation.line} "${law.name.replace(/\r?\n/g, "\\n")}"${mapping ? ` (${mapping})` : ""}`
      for (const check of checks) if (!comments.has(check.statement)) comments.set(check.statement, note)
    }
    mkdirSync(dirname(resolve(cwd, config.emit)), { recursive: true })
    writeFileSync(resolve(cwd, config.emit), render(FAST_HEADER, statements, comments))
  }
  // Everything starts under the fast imports. A proof the author supplied may
  // name lemmas from anywhere in Lean's core library, so one that fails is
  // tried again with all of it, where the installed Lean has all of it.
  const proving = performance.now()
  const generated = fresh.filter(statement => proofKind(statement) !== "authored")
  const scripted = fresh.filter(statement => proofKind(statement) === "authored")
  // A theorem with an author's script is checked in a file of its own.
  const [first, own] = await Promise.all([prove(lean, FAST_HEADER, generated), prove(lean, FAST_HEADER, scripted, undefined, true)])
  generated.forEach((statement, i) => outcomes.set(statement, first[i]!))
  scripted.forEach((statement, i) => outcomes.set(statement, own[i]!))
  const authored = scripted.filter((_, i) => !own[i]!.ok)
  if (authored.length) {
    try {
      const again = await prove(lean, FULL_HEADER, authored, undefined, true)
      authored.forEach((statement, i) => outcomes.set(statement, again[i]!))
    } catch {
      for (const statement of authored) {
        const outcome = outcomes.get(statement)!
        outcome.message += "\n(This Lean installation holds only the part of the library Pudding itself uses. A proof that needs more of it needs a full Lean: run `pudding install-lean --full`, or set PUDDING_LEAN.)"
      }
    }
  }
  report.timings.prove = Math.round(performance.now() - proving)
  // An obligation with a counterexample is false, so trying harder to prove
  // it would only waste time. The search is cheap and its result is reused
  // when the failure is explained.
  const retrying = performance.now()
  const counterexamples = new Map<Obligation, ReturnType<typeof findInput>["found"]>()
  const unexplained = new Set<string>()
  for (const { instance, obligation, checks } of pending) {
    const rejected = checks.filter(c => !outcomes.get(c.statement)!.ok)
    if (!rejected.length) continue
    const { found } = findInput(instance.binders, ir.and(obligation.guard, ir.not(obligation.claim)))
    counterexamples.set(obligation, found)
    if (!found) for (const check of rejected) unexplained.add(check.statement)
  }
  // What the default automation could not close gets a slower second attempt
  // before the rejection is reported. Lean's first message is kept, because it
  // describes the goal best.
  const retry = generated.filter((statement, i) => !first[i]!.ok && proofKind(statement) === "automatic" && unexplained.has(statement))
  const second = await prove(lean, FALLBACK_HEADER, retry.map(withFallback))
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
    const found = counterexamples.get(obligation)
    if (found) {
      const inputs = showInputs(instance.binders, found)
      if (obligation.kind === "expect") {
        const sides = obligation.sides
        entry.findings.push({
          kind: "counterexample", message: "the expectation does not hold", ...at, inputs,
          ...(sides ? { detail: `actual:   ${showValue(sides.actual, found, sides.num)}\nexpected: ${sides.negated ? "anything but " : ""}${showValue(sides.expected, found, sides.num)}` } : {}),
        })
      } else {
        // Outside what the model describes, which is not the same as throwing: the code may well return something.
        entry.findings.push(obligation.kind === "overflow" || obligation.kind === "nan" || obligation.kind === "round" || obligation.kind === "inherited" ? {
          kind: "inexact", ...at, inputs,
          message: obligation.kind === "nan" ? "this divides a number by zero, which does not give a whole number"
            : obligation.kind === "inherited" ? "this reads a property that every object inherits, which is not modeled"
            : obligation.kind === "round" ? "this number is too large for Math.round to round its quotient exactly (2^52 or beyond)"
            : "this result is too large for a number to hold exactly (beyond 2^53 - 1)",
        } : {
          kind: "throws", ...at, inputs,
          message: obligation.kind === "nothrow" ? "this divides by zero"
            : obligation.kind === "falloff" ? "this function reaches its end without returning a value"
            : obligation.kind === "missing" ? "this reads a property the object does not have"
            : obligation.kind === "null" ? "this reads a property of null, or calls it"
            : obligation.kind === "undefined" ? "this reads a property of undefined, or calls it" : "this throw is reached",
        })
      }
    } else if (rejected.message.includes("(kernel) deep recursion detected")) {
      // Lean gave up on the size of the values, which says nothing about the
      // law. It is reported as not proved, with what executing it showed.
      law.problem ??= { kind: "unsupported", message: "the values here are too large to check: Lean ran out of depth on them", ...at }
    } else {
      const message = obligation.kind === "expect" ? "Lean could not prove this, and no counterexample was found"
        : obligation.kind === "nothrow" || obligation.kind === "nan" ? "Lean could not prove that the divisor is never zero"
        : obligation.kind === "overflow" ? "Lean could not prove that this result stays small enough for a number to hold exactly"
        : obligation.kind === "round" ? "Lean could not prove that this number stays small enough for Math.round to round its quotient exactly"
        : obligation.kind === "null" ? "Lean could not prove that this value is never null"
        : obligation.kind === "undefined" ? "Lean could not prove that this value is never undefined"
        : obligation.kind === "falloff" ? "Lean could not prove that this function always returns a value"
        : obligation.kind === "missing" ? "Lean could not prove that this key is always a property of the object"
        : obligation.kind === "inherited" ? "Lean could not prove that this key never names a property every object inherits"
        : "Lean could not prove that this throw is never reached"
      const mapping = instance.binders.filter(b => b.label !== b.name).map(b => `${b.name} = ${b.label}`).join(", ")
      const leanDetail = rejected.message.split("\n").slice(0, 8).join("\n")
      entry.findings.push({ kind: "unproved", message, ...at, detail: mapping ? `where ${mapping}\n${leanDetail}` : leanDetail })
    }
  }

  // An expectation whose condition can never be true proves nothing.
  const vacuityChecks: { entry: LawReport; site: { file: string; line: number; column: number; text: string }; law: Law; checks: Check[] }[] = []
  for (const law of laws) {
    if (law.problem || law.mode !== "run") continue
    const entry = lawReports.get(law)!
    for (const [key, site] of law.expectSites) {
      const reaching = law.instances.flatMap(instance => instance.obligations
        .filter(o => o.kind === "expect" && `${o.file}:${o.line}:${o.column}` === key).map(obligation => ({ instance, obligation })))
      const vacuous = () => entry.findings.push({
        kind: "vacuous", message: "this expectation is never reached, so it proves nothing", ...site,
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
        entry.findings.push({ kind: "vacuous", message: "the condition guarding this expectation is never true, so it proves nothing", ...site })
      } else entry.notes.push(`line ${site.line}: no input satisfying the condition was found by sampling`)
    }
  }

  // Compare the model that was proved with what the real code did.
  const executedOnly = new Map<Law, boolean>()
  if (job && execution) {
    const { outcomes, timedOut } = await execution
    for (const { file } of job.files) {
      const outcome = outcomes.get(file)
      for (const note of outcome?.rerouted ?? []) {
        report.warnings.push(`the laws ran against the files TypeScript read, which are not the ones Node would load: ${note.replaceAll(cwd + "/", "").replaceAll(cwd + "\\", "")}`)
      }
      const reason = outcome?.error ?? (outcome ? undefined : timedOut ? `executing the laws took longer than ${RUNTIME_TIMEOUT_MS / 1000} s` : "the worker that executes laws stopped unexpectedly")
      if (outcome?.throws) {
        // The file itself fails when it is loaded, so nothing in it holds at run time, whatever was proved about the model.
        for (const law of candidates.filter(candidate => candidate.file === file && candidate.mode === "run")) {
          lawReports.get(law)!.findings.push({
            kind: "throws", message: `the law file throws when it is loaded (${reason})`, file: law.file, line: law.line, column: law.column,
          })
        }
      } else if (outcome?.miscounted) {
        // Laws that exist at run time but were never read would otherwise go unchecked without a word.
        report.errors.push(`${displayPath(cwd, file)} registers ${outcome.miscounted.ran} ${outcome.miscounted.ran === 1 ? "law" : "laws"} when it runs, but Pudding read ${outcome.miscounted.read} from it; write each law as a plain law() or describe() call`)
      } else if (reason) report.warnings.push(`${displayPath(cwd, file)} was not compared with the running code: ${reason}`)
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
        // Inputs that leave out part of the declared domain are never every input, however few there are.
        if (law.problem && result.executed) executedOnly.set(law, result.exhaustive && !law.narrowed)
        // Lean accepted every theorem of this law, yet the model those theorems describe fails here.
        if (!law.problem && !entry.findings.length && result.modelFails) {
          entry.findings.push({
            kind: "mismatch", inputs: result.modelFails, file: law.file, line: law.line, column: law.column,
            message: "Lean accepted the proof, but evaluating the same model on this input says the law fails; the proof cannot be trusted",
          })
        }
      }
    }
  }

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
    saveProofs(known, [...used].filter(key => !proved.has(key)))
    const saved: Cache = { version: CACHE_VERSION, lean: cache.lean }
    if (JSON.stringify(saved) !== JSON.stringify(loadCache(cacheFile))) {
      mkdirSync(dirname(cacheFile), { recursive: true })
      replaceFile(cacheFile, JSON.stringify(saved))
    }
  }
  return report
}
