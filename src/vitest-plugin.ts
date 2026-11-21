// Vitest plugin and globalSetup that proves every law file in one Pudding run
// in the main process and hands each worker its file's results.

import { existsSync, mkdtempSync, renameSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join, resolve } from "node:path"
import { fileURLToPath } from "node:url"
import type { Config } from "./index.ts"
import { createWatchSession, run, type LawReport, type WatchSession } from "./runner.ts"

const DEFAULT_VITEST_INCLUDE = ["**/*.{test,spec}.?(c|m)[jt]s?(x)"]
const DEFAULT_LAW_INCLUDE = ["**/*.law.ts"]

export interface PuddingPluginOptions extends Config {
  /** Glob patterns added to Vitest's `test.include`. Default: `["**\/*.law.ts"]`. */
  lawInclude?: string[]
}

export interface PrecomputedReport {
  root: string
  errors: string[]
  lawsByFile: Record<string, LawReport[]>
  runs: number
}

interface PluginState {
  options: PuddingPluginOptions
  changed: Set<string>
  session?: WatchSession
}

const states = new Map<string, PluginState>()
const OPTIONS_ENV = "PUDDING_VITEST_PLUGIN_OPTIONS"

function stateFor(root: string): PluginState {
  const key = resolve(root)
  let state = states.get(key)
  if (!state) {
    let options: PuddingPluginOptions = {}
    const raw = process.env[OPTIONS_ENV]
    if (raw) {
      try { options = JSON.parse(raw) as PuddingPluginOptions } catch { /* ignore */ }
    }
    state = { options, changed: new Set() }
    states.set(key, state)
  }
  return state
}

function writeSnapshot(file: string, data: PrecomputedReport): void {
  const tmp = `${file}.${process.pid}.tmp`
  writeFileSync(tmp, JSON.stringify(data))
  renameSync(tmp, file)
}

function isLawPath(file: string): boolean {
  return /\.law\.[mc]?[jt]sx?$/.test(file)
}

interface GlobalSetupProject {
  config?: { root?: string }
  provide(key: string, value: unknown): void
  onTestsRerun?(cb: (specs: readonly (string | { moduleId?: string })[]) => void | Promise<void>): void
}

interface VitestConfigLike {
  root?: string
  test?: {
    include?: string[]
    globalSetup?: string | string[]
  }
}

interface ViteServerLike {
  config?: { root?: string }
  watcher?: {
    on(event: string, listener: (file: string) => void): void
  }
}

/**
 * Vitest plugin: adds `**\/*.law.ts` to `test.include`, proves all law files
 * once in global setup, hands each worker its file's results, and re-runs only
 * affected law files on edits in watch mode.
 */
export function pudding(options: PuddingPluginOptions = {}): {
  name: string
  config(userConfig: VitestConfigLike): VitestConfigLike
  configureServer(server: ViteServerLike): void
} {
  const setupFile = fileURLToPath(import.meta.url)
  const lawInclude = options.lawInclude ?? DEFAULT_LAW_INCLUDE
  const { lawInclude: _ignored, ...runOptions } = options

  return {
    name: "pudding",
    config(userConfig) {
      const root = resolve(userConfig.root ?? process.cwd())
      states.set(root, { options: runOptions, changed: new Set() })
      process.env[OPTIONS_ENV] = JSON.stringify(runOptions)

      const existingInclude = userConfig.test?.include ?? DEFAULT_VITEST_INCLUDE
      const include = [...new Set([...existingInclude, ...lawInclude])]
      const existingSetup = userConfig.test?.globalSetup
      const setups = Array.isArray(existingSetup) ? existingSetup : existingSetup ? [existingSetup] : []
      const globalSetup = setups.includes(setupFile) ? setups : [...setups, setupFile]
      return {
        test: {
          include,
          globalSetup,
        },
      }
    },
    configureServer(server) {
      const root = resolve(server.config?.root ?? process.cwd())
      const state = stateFor(root)
      server.watcher?.on("change", file => state.changed.add(resolve(file)))
      server.watcher?.on("add", file => state.changed.add(resolve(file)))
      server.watcher?.on("unlink", file => state.changed.add(resolve(file)))
    },
  }
}

/** Vitest globalSetup entry point registered automatically by `pudding()`. */
export async function setup(project: GlobalSetupProject): Promise<() => void> {
  const root = resolve(project.config?.root ?? process.cwd())
  const state = stateFor(root)
  const session = createWatchSession()
  state.session = session

  const dir = mkdtempSync(join(tmpdir(), "pudding-vitest-"))
  const reportFile = join(dir, "report.json")

  const snapshot: PrecomputedReport = { root, errors: [], lawsByFile: {}, runs: 0 }

  const mergeReport = (report: Awaited<ReturnType<typeof run>>, replacedFiles?: readonly string[]) => {
    snapshot.runs++
    snapshot.errors = report.errors
    if (!replacedFiles) snapshot.lawsByFile = {}
    else for (const file of replacedFiles) delete snapshot.lawsByFile[resolve(file)]
    for (const entry of report.laws) {
      const key = resolve(entry.file)
      const list = snapshot.lawsByFile[key] ?? []
      list.push(entry)
      snapshot.lawsByFile[key] = list
    }
    writeSnapshot(reportFile, snapshot)
  }

  const initial = await run({ ...state.options, cwd: root, session })
  // If a project has unit tests and no law files yet, do not fail the Vitest run.
  if (initial.errors.length === 1 && initial.errors[0] === "no law files were found") {
    snapshot.runs++
    writeSnapshot(reportFile, snapshot)
  } else {
    mergeReport(initial)
  }

  project.provide("puddingReportFile", reportFile)

  project.onTestsRerun?.(async specs => {
    const changed = [...state.changed]
    state.changed.clear()
    const rerunLawFiles = new Set<string>()
    for (const spec of specs) {
      const id = typeof spec === "string" ? spec : spec?.moduleId
      if (id && isLawPath(id) && existsSync(id)) rerunLawFiles.add(resolve(id))
    }
    let needFull = false
    for (const file of changed) {
      if (file.endsWith(".json") || /pudding\.config\./.test(file) || !existsSync(file)) {
        needFull = true
        break
      }
      const affected = session.affected(file)
      if (!affected) {
        if (isLawPath(file)) needFull = true
        continue
      }
      for (const lawFile of affected) if (existsSync(lawFile)) rerunLawFiles.add(resolve(lawFile))
    }
    if (needFull) {
      session.close()
      const next = await run({ ...state.options, cwd: root, session })
      mergeReport(next)
      return
    }
    if (!rerunLawFiles.size) return
    const lawFiles = [...rerunLawFiles].sort()
    const next = await run({ ...state.options, cwd: root, session, lawFiles, ...(changed.length ? { changedFiles: changed } : {}) })
    mergeReport(next, lawFiles)
  })

  return () => {
    session.close()
    states.delete(root)
    rmSync(dir, { recursive: true, force: true })
  }
}
