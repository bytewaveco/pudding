import { realpathSync } from 'node:fs'
import { registerHooks } from 'node:module'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { parentPort, workerData } from 'node:worker_threads'

import * as ir from './ir.ts'
import { assignments, showInputs, valuePool } from './search.ts'

import type { Binder, Expr, Scalar } from './ir.ts'
import type { ArgShape } from './translate.ts'

export interface RuntimeMap {
  resolutions: Map<string, Map<string, string>>
  edits: Map<string, [number, number, string][]>
}

interface Instance {
  binders: Binder[]
  arg: ArgShape | undefined
  obligations: { guard: Expr; claim: Expr; inexact: boolean }[]
  defs?: ir.FnDef[]
}

export interface Job {
  map: RuntimeMap
  budget: number
  files: {
    file: string
    registered: number
    laws: {
      index: number
      unproved: boolean
      budget?: number
      instances: Instance[]
      mentioned: Expr[]
    }[]
  }[]
}

export interface LawOutcome {
  index: number
  executed: number
  exhaustive: boolean
  failure?: {
    kind: 'counterexample' | 'mismatch'
    inputs: Record<string, string>
    actual: boolean
    expected: boolean
  }
  modelFails?: Record<string, string>
}

export interface FileOutcome {
  file: string
  error?: string
  throws?: boolean
  rerouted?: string[]
  miscounted?: { ran: number; read: number }
  laws: LawOutcome[]
}

interface Registered {
  name: string
  callback: ((input: unknown) => void) | undefined
}

const pathOf = (url: string) => fileURLToPath(url.split('?')[0]!)

function compileArgument(
  shape: ArgShape,
  binders: ReadonlyMap<string, Binder>,
): (env: Map<string, Scalar>) => unknown {
  const emit = (s: ArgShape): string => {
    switch (s.k) {
      case 'binder': {
        const b = binders.get(s.name)

        if (b && ir.isListTy(b.ty)) {
          return b.num
            ? `(env.get(${JSON.stringify(s.name)})).map(Number)`
            : `[...(env.get(${JSON.stringify(s.name)}))]`
        }

        return b?.num
          ? `Number(env.get(${JSON.stringify(s.name)}))`
          : `env.get(${JSON.stringify(s.name)})`
      }
      case 'const':
        return s.num
          ? String(Number(s.value))
          : typeof s.value === 'bigint'
            ? `${s.value}n`
            : JSON.stringify(s.value)
      case 'undefined':
        return 'undefined'
      case 'null':
        return 'null'
      case 'array':
        return `[${s.items.map(emit).join(',')}]`
      case 'record':
        return `({${s.fields.map(([key, field]) => `${key === '__proto__' ? '["__proto__"]' : JSON.stringify(key)}:${emit(field)}`).join(',')}})`
    }
  }

  return new Function('env', `return ${emit(shape)}`) as (env: Map<string, Scalar>) => unknown
}

interface CompiledObligation {
  guard: (env: ReadonlyMap<string, Scalar>) => Scalar
  claim: (env: ReadonlyMap<string, Scalar>) => Scalar
  inexact: boolean
}

function modelHolds(
  obligations: readonly CompiledObligation[],
  env: Map<string, Scalar>,
): boolean | 'outside' {
  try {
    let holds = true

    for (const obligation of obligations) {
      if (obligation.guard(env) !== true || obligation.claim(env) === true) continue
      if (obligation.inexact) return 'outside'
      holds = false
    }

    return holds
  } catch (error) {
    if (error instanceof ir.RecursionLimitError) return 'outside'
    if (error instanceof ir.EvaluationError) return false
    throw error
  }
}

function runtimeHolds(callback: (input: unknown) => void, argument: unknown): boolean {
  try {
    const result: unknown = callback(argument)
    if (typeof (result as { then?: unknown } | null | undefined)?.then === 'function') return false
    return true
  } catch {
    return false
  }
}

async function register(
  file: string,
): Promise<Registered[] | { message: string; throws: boolean }> {
  const key = Symbol.for('pudding.registry')
  const registry: Registered[] = []
  const globals = globalThis as Record<symbol, unknown>
  globals[key] = registry

  try {
    await import(pathToFileURL(file).href)
    return registry
  } catch (error) {
    const stack = error instanceof Error ? (error.stack ?? '') : ''
    const throws =
      !(error instanceof Error) ||
      /\n\s+at [^\n]*file:\/\/(?![^\n]*[\\/]node_modules[\\/])/.test(stack)
    const text =
      error instanceof Error ? `${error.name}: ${error.message.split('\n')[0]!}` : String(error)
    return { message: text, throws }
  } finally {
    delete globals[key]
  }
}

async function execute(job: Job, report: (outcome: FileOutcome) => void) {
  const rerouted = new Set<string>()
  registerHooks({
    resolve(specifier, context, nextResolve) {
      const target = context.parentURL?.startsWith('file:')
        ? job.map.resolutions.get(pathOf(context.parentURL))?.get(specifier)
        : undefined
      if (!target) return nextResolve(specifier, context)

      try {
        const native = nextResolve(specifier, context).url

        if (native.startsWith('file:') && realpathSync(pathOf(native)) !== realpathSync(target)) {
          rerouted.add(
            `\`${specifier}\` in ${pathOf(context.parentURL!)}: Node resolves it to ${pathOf(native)}, TypeScript read ${target}`,
          )
        }
      } catch {}

      return { url: pathToFileURL(target).href, shortCircuit: true }
    },
    load(url, context, nextLoad) {
      const result = nextLoad(url, context)
      const edits = url.startsWith('file:') ? job.map.edits.get(pathOf(url)) : undefined
      if (!edits || result.source === undefined || result.source === null) return result
      let text =
        typeof result.source === 'string'
          ? result.source
          : Buffer.from(result.source as Uint8Array).toString('utf8')
      const ordered = [...edits].sort((a, b) => b[0] - a[0])

      for (const [start, end, replacement] of ordered) {
        const original = text.slice(start, end)

        if (!replacement)
          text = text.slice(0, start) + original.replace(/[^\n]/g, ' ') + text.slice(end)
        else {
          const newlines =
            (original.match(/\n/g)?.length ?? 0) - (replacement.match(/\n/g)?.length ?? 0)
          text =
            text.slice(0, start) +
            replacement +
            (newlines > 0 ? '\n'.repeat(newlines) : '') +
            text.slice(end)
        }
      }

      return { ...result, source: text }
    },
  })

  for (const { file, registered, laws } of job.files) {
    const outcome: FileOutcome = { file, laws: [] }
    const runtime = await register(file)

    if (!Array.isArray(runtime)) {
      outcome.error = runtime.throws
        ? runtime.message
        : `it could not be executed (${runtime.message})`
      outcome.throws = runtime.throws
    } else if (runtime.length !== registered)
      outcome.miscounted = { ran: runtime.length, read: registered }
    else {
      for (const law of laws) {
        const callback = runtime[law.index]?.callback
        if (!callback) continue
        const result: LawOutcome = { index: law.index, executed: 0, exhaustive: true }

        for (const instance of law.instances) {
          const binderMap = new Map(instance.binders.map((b) => [b.name, b]))
          const buildArg = instance.arg ? compileArgument(instance.arg, binderMap) : undefined
          const defsMap = instance.defs?.length
            ? new Map(instance.defs.map((d) => [d.name, d]))
            : undefined
          const compiled = law.unproved
            ? []
            : instance.obligations.map((o) => ({
                guard: ir.compile(o.guard, defsMap),
                claim: ir.compile(o.claim, defsMap),
                inexact: o.inexact,
              }))
          const space = assignments(
            instance.binders,
            valuePool([
              ...instance.obligations.flatMap((o) => [o.guard, o.claim]),
              ...law.mentioned,
            ]),
            law.budget ?? job.budget,
          )
          result.exhaustive &&= space.exhaustive
          space.each((env) => {
            const expected = law.unproved ? true : modelHolds(compiled, env)

            if (expected === 'outside') {
              result.exhaustive = false
              return false
            }

            if (expected === false) result.modelFails ??= showInputs(instance.binders, env)
            result.executed++
            const actual = runtimeHolds(callback, buildArg ? buildArg(env) : undefined)
            if (actual === expected) return false
            result.failure = {
              kind: law.unproved ? 'counterexample' : 'mismatch',
              inputs: showInputs(instance.binders, env),
              actual,
              expected,
            }
            return true
          })
          if (result.failure) break
        }

        outcome.laws.push(result)
      }
    }

    if (rerouted.size) outcome.rerouted = [...rerouted]
    rerouted.clear()
    report(outcome)
  }
}

if (parentPort) {
  const port = parentPort
  await execute(workerData as Job, (outcome) => port.postMessage(outcome))
  port.postMessage('done')
}
