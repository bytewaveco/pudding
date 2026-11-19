// Runs in a worker thread. Executes each law against the real code and
// compares the outcome with the model the proofs are about.

import { registerHooks } from "node:module"
import { fileURLToPath, pathToFileURL } from "node:url"
import { parentPort, workerData } from "node:worker_threads"
import * as ir from "./ir.ts"
import type { Binder, Expr, Scalar } from "./ir.ts"
import { assignments, showInputs, valuePool } from "./search.ts"
import type { ArgShape } from "./translate.ts"

export interface RuntimeMap {
  /** For each source file, where each of its import specifiers resolves. */
  resolutions: Map<string, Map<string, string>>
  /** For each source file, the text ranges of imported or exported names that are types only. */
  elided: Map<string, [number, number][]>
}

interface Instance {
  binders: Binder[]
  arg: ArgShape | undefined
  obligations: { guard: Expr; claim: Expr; inexact: boolean }[]
}

export interface Job {
  map: RuntimeMap
  /** The most inputs to try per law instance. */
  budget: number
  files: {
    file: string
    /** How many laws the translator saw; a different count at run time means the two cannot be paired up. */
    registered: number
    /** `mentioned` holds the constants of a law that could not be translated, so sampling can still aim at them. */
    laws: { index: number; unproved: boolean; instances: Instance[]; mentioned: Expr[] }[]
  }[]
}

export interface LawOutcome {
  index: number
  executed: number
  exhaustive: boolean
  failure?: { kind: "counterexample" | "mismatch"; inputs: Record<string, string>; actual: boolean; expected: boolean }
  /** An input for which the model itself says the law fails. If Lean accepted the law, something is wrong. */
  modelFails?: Record<string, string>
}

export interface FileOutcome {
  file: string
  /** Why the file's laws could not be executed. */
  error?: string
  /** True when the file itself throws while it loads, as opposed to Node being unable to run TypeScript like it. */
  throws?: boolean
  /** Set when the file registered a different number of laws than were read from its source. */
  miscounted?: { ran: number; read: number }
  laws: LawOutcome[]
}

/** Failures that say Node could not run the source as written, not that the code is wrong. */
const TOOLING = new Set([
  "ERR_MODULE_NOT_FOUND", "ERR_UNSUPPORTED_TYPESCRIPT_SYNTAX", "ERR_INVALID_TYPESCRIPT_SYNTAX", "ERR_UNSUPPORTED_NODE_MODULES_TYPE_STRIPPING",
  "ERR_UNKNOWN_FILE_EXTENSION", "ERR_PACKAGE_PATH_NOT_EXPORTED", "ERR_UNSUPPORTED_DIR_IMPORT", "ERR_IMPORT_ATTRIBUTE_MISSING", "ERR_REQUIRE_ESM",
  "ERR_UNSUPPORTED_ESM_URL_SCHEME", "ERR_UNKNOWN_BUILTIN_MODULE",
])

interface Registered {
  name: string
  callback: ((input: unknown) => void) | undefined
}

const pathOf = (url: string) => fileURLToPath(url.split("?")[0]!)

function buildArgument(shape: ArgShape, env: Map<string, Scalar>, numbers: Set<string>): unknown {
  switch (shape.k) {
    case "binder": return numbers.has(shape.name) ? Number(env.get(shape.name)) : env.get(shape.name)
    case "const": return shape.num ? Number(shape.value) : shape.value
    case "array": return shape.items.map(item => buildArgument(item, env, numbers))
    case "record": return Object.fromEntries(shape.fields.map(([key, field]) => [key, buildArgument(field, env, numbers)]))
  }
}

/**
 * What the model says about an input: whether the law holds, or that the
 * model does not describe this input. The latter is when a number leaves the
 * range of exact whole numbers; the real code then computes something the
 * model has no counterpart for, and that is already reported on its own.
 */
function modelHolds(instance: Instance, env: Map<string, Scalar>): boolean | "outside" {
  try {
    let holds = true
    for (const obligation of instance.obligations) {
      if (ir.evaluate(obligation.guard, env) !== true || ir.evaluate(obligation.claim, env) === true) continue
      if (obligation.inexact) return "outside"
      holds = false
    }
    return holds
  } catch (error) {
    if (error instanceof ir.EvaluationError) return false
    throw error
  }
}

function runtimeHolds(callback: (input: unknown) => void, argument: unknown): boolean {
  try {
    callback(argument)
    return true
  } catch {
    return false
  }
}

async function register(file: string): Promise<Registered[] | { message: string; throws: boolean }> {
  const key = Symbol.for("pudding.registry")
  const registry: Registered[] = []
  const globals = globalThis as Record<symbol, unknown>
  globals[key] = registry
  try {
    await import(pathToFileURL(file).href)
    return registry
  } catch (error) {
    const code = (error as { code?: unknown } | null)?.code
    // A SyntaxError is Node's when it comes from linking modules. One raised by the code itself, by JSON.parse say, is the code failing.
    const linking = error instanceof SyntaxError && /does not provide an export named|The requested module/.test(error.message)
    const tooling = linking || (typeof code === "string" && TOOLING.has(code))
    const text = error instanceof Error ? `${error.name}: ${error.message.split("\n")[0]!}` : String(error)
    return { message: text, throws: !tooling }
  } finally {
    delete globals[key]
  }
}

async function execute(job: Job, report: (outcome: FileOutcome) => void) {
  registerHooks({
    resolve(specifier, context, nextResolve) {
      const target = context.parentURL?.startsWith("file:") ? job.map.resolutions.get(pathOf(context.parentURL))?.get(specifier) : undefined
      return target ? { url: pathToFileURL(target).href, shortCircuit: true } : nextResolve(specifier, context)
    },
    load(url, context, nextLoad) {
      const result = nextLoad(url, context)
      const ranges = url.startsWith("file:") ? job.map.elided.get(pathOf(url)) : undefined
      if (!ranges || result.source === undefined || result.source === null) return result
      // Blank the names rather than cut them, so positions in error messages stay true.
      let text = typeof result.source === "string" ? result.source : Buffer.from(result.source as Uint8Array).toString("utf8")
      for (const [start, end] of ranges) text = text.slice(0, start) + text.slice(start, end).replace(/[^\n]/g, " ") + text.slice(end)
      return { ...result, source: text }
    },
  })
  for (const { file, registered, laws } of job.files) {
    const outcome: FileOutcome = { file, laws: [] }
    const runtime = await register(file)
    if (!Array.isArray(runtime)) {
      outcome.error = runtime.throws ? runtime.message : `it could not be executed (${runtime.message})`
      outcome.throws = runtime.throws
    } else if (runtime.length !== registered) outcome.miscounted = { ran: runtime.length, read: registered }
    else {
      for (const law of laws) {
        const callback = runtime[law.index]?.callback
        if (!callback) continue
        const result: LawOutcome = { index: law.index, executed: 0, exhaustive: true }
        for (const instance of law.instances) {
          const numbers = new Set(instance.binders.filter(b => b.num).map(b => b.name))
          const space = assignments(instance.binders, valuePool([...instance.obligations.flatMap(o => [o.guard, o.claim]), ...law.mentioned]), job.budget)
          result.exhaustive &&= space.exhaustive
          space.each(env => {
            const expected = law.unproved ? true : modelHolds(instance, env)
            if (expected === "outside") return false
            if (expected === false) result.modelFails ??= showInputs(instance.binders, env)
            result.executed++
            const actual = runtimeHolds(callback, instance.arg ? buildArgument(instance.arg, env, numbers) : undefined)
            if (actual === expected) return false
            result.failure = { kind: law.unproved ? "counterexample" : "mismatch", inputs: showInputs(instance.binders, env), actual, expected }
            return true
          })
          if (result.failure) break
        }
        outcome.laws.push(result)
      }
    }
    report(outcome)
  }
}

if (parentPort) {
  const port = parentPort
  await execute(workerData as Job, outcome => port.postMessage(outcome))
  port.postMessage("done")
}
