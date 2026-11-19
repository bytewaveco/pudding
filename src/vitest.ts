// The bridge to Vitest. When a law file is collected by Vitest, each law
// becomes a test whose result is the law's proof. Pudding runs once per file,
// when the file's first test starts.

import { resolve } from "node:path"
import { describe as suite, expect as vitestExpect, test } from "vitest"
import type { LawReport, Report } from "./runner.ts"

export type Modifier = "run" | "skip" | "only" | "todo"

/** A whole file is proved in one run, and proving starts cold, so allow far longer than a unit test gets. */
const TIMEOUT_MS = 120_000

/** What the bridge reads of a Vitest task. */
interface Task {
  type: string
  name: string
  tasks?: Task[]
  suite?: Task
  file: Task & { filepath: string }
}

const groups: string[] = []
// Keyed by the file's task, which Vitest makes anew each time it collects the
// file, so a rerun in the same worker proves the file again.
const runs = new WeakMap<Task, Promise<Report>>()

function root(): string {
  const worker = (globalThis as { __vitest_worker__?: { config?: { root?: string } } }).__vitest_worker__
  return worker?.config?.root ?? process.cwd()
}

function proofs(file: Task["file"]): Promise<Report> {
  let pending = runs.get(file)
  if (!pending) {
    pending = import("./runner.ts").then(({ run }) => run({ cwd: root(), lawFiles: [file.filepath] }))
    runs.set(file, pending)
  }
  return pending
}

const path = (task: Task): string[] => (task.suite && task.suite !== task.file ? [...path(task.suite), task.name] : [task.name])
const tests = (task: Task): Task[] => (task.tasks ?? []).flatMap(child => (child.type === "test" ? [child] : tests(child)))

/**
 * Whether Vitest is collecting a test file right now. The `VITEST` variable
 * alone does not say so: every process a test starts inherits it.
 */
export function collecting(): boolean {
  try {
    return typeof vitestExpect.getState().testPath === "string"
  } catch {
    return false
  }
}

/** An error that reads like Pudding's own report and points at the line in the law file. */
function failure(entry: LawReport): Error {
  const lines: string[] = []
  for (const finding of entry.findings) {
    lines.push(finding.message)
    if (finding.text) lines.push(`  ${finding.text}`)
    if (finding.inputs && Object.keys(finding.inputs).length) {
      lines.push(`  with ${Object.entries(finding.inputs).map(([name, value]) => `${name} = ${value}`).join(", ")}`)
    }
    if (finding.detail) lines.push(...finding.detail.split("\n").map(line => `  ${line}`))
  }
  const error = new Error(lines.join("\n"))
  error.name = "LawFailed"
  const at = entry.findings[0] ?? entry
  error.stack = `${error.name}: ${error.message}\n    at ${at.file}:${at.line}:${at.column}`
  return error
}

export function defineLaw(modifier: Modifier, name: string): void {
  if (modifier === "todo") return void test.todo(name)
  const full = [...groups, name].join(" > ")
  const define = modifier === "skip" ? test.skip : modifier === "only" ? test.only : test
  define(name, async context => {
    const task = context.task as unknown as Task
    const report = await proofs(task.file)
    if (report.errors.length) throw new Error(report.errors.join("\n"))
    // Laws are matched to the report by name, and by order among laws that share one.
    const occurrence = tests(task.file).filter(other => path(other).join(" > ") === full).indexOf(task)
    const entry = report.laws.filter(law => resolve(law.file) === resolve(task.file.filepath) && law.name === full)[occurrence]
    if (!entry) throw new Error(`Pudding did not read a law named "${full}" in this file`)
    if (entry.status === "failed") throw failure(entry)
    const annotate = (context as { annotate?: (message: string) => Promise<unknown> }).annotate
    if (annotate) {
      if (entry.status === "checked") await annotate.call(context, "executed for every input, not proved")
      if (entry.status === "sampled") await annotate.call(context, "executed on sampled inputs, not proved")
      for (const note of entry.notes) await annotate.call(context, note)
    }
  }, TIMEOUT_MS)
}

export function defineGroup(modifier: Exclude<Modifier, "todo">, name: string, body: () => void): void {
  const define = modifier === "skip" ? suite.skip : modifier === "only" ? suite.only : suite
  define(name, () => {
    groups.push(name)
    try {
      body()
    } finally {
      groups.pop()
    }
  })
}
