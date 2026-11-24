import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe as suite, expect as vitestExpect, inject, test } from 'vitest'

import type { LawReport, Report } from './runner.ts'
import type { PrecomputedReport } from './vitest-plugin.ts'

export type Modifier = 'run' | 'skip' | 'only' | 'todo'

const TIMEOUT_MS = 120_000

interface Task {
  type: string
  name: string
  tasks?: Task[]
  suite?: Task
  file: Task & { filepath: string }
}

const groups: string[] = []
const runs = new WeakMap<Task, Promise<Report>>()

function root(): string {
  const worker = (globalThis as { __vitest_worker__?: { config?: { root?: string } } })
    .__vitest_worker__
  return worker?.config?.root ?? process.cwd()
}

function precomputed(filepath: string): Report | undefined {
  let reportFile: string | undefined

  try {
    reportFile = inject('puddingReportFile' as never) as string | undefined
  } catch {
    return undefined
  }

  if (!reportFile) return undefined

  try {
    const data = JSON.parse(readFileSync(reportFile, 'utf8')) as PrecomputedReport
    const key = resolve(filepath)
    const laws = data.lawsByFile[key]
    if (!laws && !data.errors.length) return undefined
    return {
      ok: !data.errors.length && (laws ?? []).every((l) => l.status !== 'failed'),
      laws: laws ?? [],
      errors: data.errors,
      warnings: [],
      counts: { proved: 0, checked: 0, sampled: 0, failed: 0, skipped: 0, todo: 0 },
      obligations: 0,
      cachedObligations: 0,
      cases: 0,
      durationMs: 0,
      retried: 0,
      timings: { typescript: 0, prove: 0, retry: 0, crossCheck: 0 },
      lean: '',
      compiler: '',
    }
  } catch {
    return undefined
  }
}

function proofs(file: Task['file']): Promise<Report> {
  let pending = runs.get(file)

  if (!pending) {
    const ready = precomputed(file.filepath)
    pending = ready
      ? Promise.resolve(ready)
      : import('./runner.ts').then(({ run }) => run({ cwd: root(), lawFiles: [file.filepath] }))
    runs.set(file, pending)
  }

  return pending
}

const path = (task: Task): string[] =>
  task.suite && task.suite !== task.file ? [...path(task.suite), task.name] : [task.name]

const tests = (task: Task): Task[] =>
  (task.tasks ?? []).flatMap((child) => (child.type === 'test' ? [child] : tests(child)))

export function collecting(): boolean {
  try {
    return typeof vitestExpect.getState().testPath === 'string'
  } catch {
    return false
  }
}

function failure(entry: LawReport): Error {
  const lines: string[] = []

  for (const finding of entry.findings) {
    lines.push(finding.message)
    if (finding.text) lines.push(`  ${finding.text}`)

    if (finding.inputs && Object.keys(finding.inputs).length) {
      lines.push(
        `  with ${Object.entries(finding.inputs)
          .map(([name, value]) => `${name} = ${value}`)
          .join(', ')}`,
      )
    }

    if (finding.detail) lines.push(...finding.detail.split('\n').map((line) => `  ${line}`))
  }

  const error = new Error(lines.join('\n'))
  error.name = 'LawFailed'
  const at = entry.findings[0] ?? entry
  error.stack = `${error.name}: ${error.message}\n    at ${at.file}:${at.line}:${at.column}`
  return error
}

export function defineLaw(modifier: Modifier, name: string): void {
  if (modifier === 'todo') return void test.todo(name)
  const full = [...groups, name].join(' > ')
  const define = modifier === 'skip' ? test.skip : modifier === 'only' ? test.only : test
  define(
    name,
    async (context) => {
      const task = context.task as unknown as Task
      const report = await proofs(task.file)
      if (report.errors.length) throw new Error(report.errors.join('\n'))
      const occurrence = tests(task.file)
        .filter((other) => path(other).join(' > ') === full)
        .indexOf(task)
      const entry = report.laws.filter(
        (law) => resolve(law.file) === resolve(task.file.filepath) && law.name === full,
      )[occurrence]
      if (!entry) throw new Error(`Pudding did not read a law named "${full}" in this file`)
      if (entry.status === 'failed') throw failure(entry)
      const annotate = (context as { annotate?: (message: string) => Promise<unknown> }).annotate

      if (annotate) {
        if (entry.status === 'checked')
          await annotate.call(context, 'executed for every input, not proved')

        if (entry.status === 'sampled')
          await annotate.call(context, 'executed on sampled inputs, not proved')

        for (const note of entry.notes) await annotate.call(context, note)
      }

      if (entry.status === 'checked' || entry.status === 'sampled') {
        const summary =
          entry.status === 'checked'
            ? 'executed for every input, not proved'
            : 'executed on sampled inputs, not proved'
        const reason = entry.notes[0] ? ` (${entry.notes[0]})` : ''
        console.warn(`[pudding] ~ ${full}: ${summary}${reason}`)
      }
    },
    TIMEOUT_MS,
  )
}

export function defineGroup(
  modifier: Exclude<Modifier, 'todo'>,
  name: string,
  body: () => void,
): void {
  const define = modifier === 'skip' ? suite.skip : modifier === 'only' ? suite.only : suite
  define(name, () => {
    groups.push(name)

    try {
      body()
    } finally {
      groups.pop()
    }
  })
}
