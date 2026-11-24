import { existsSync, mkdtempSync, renameSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve, sep } from 'node:path'
import { fileURLToPath } from 'node:url'

import { createWatchSession, run, type LawReport, type WatchSession } from './runner.ts'

import type { Config } from './index.ts'

const DEFAULT_VITEST_INCLUDE = ['**/*.{test,spec}.?(c|m)[jt]s?(x)']
const DEFAULT_LAW_INCLUDE = ['**/*.law.ts']

export interface PuddingPluginOptions extends Config {
  lawInclude?: string[]
}

export interface PrecomputedReport {
  root: string
  errors: string[]
  lawsByFile: Record<string, LawReport[]>
  runs: number
}

interface PluginState {
  root: string
  name: string
  options: PuddingPluginOptions
  changed: Set<string>
  session?: WatchSession
}

const states = new Map<string, PluginState>()
const OPTIONS_ENV = 'PUDDING_VITEST_PLUGIN_OPTIONS'

function projectNameOf(raw: unknown): string {
  if (typeof raw === 'string') return raw

  if (
    raw &&
    typeof raw === 'object' &&
    'label' in raw &&
    typeof (raw as { label?: unknown }).label === 'string'
  ) {
    return (raw as { label: string }).label
  }

  return ''
}

function stateKey(root: string, name: string): string {
  return `${resolve(root)}\0${name}`
}

function readEnvOptionsMap(): Record<string, PuddingPluginOptions> {
  const raw = process.env[OPTIONS_ENV]
  if (!raw) return {}

  try {
    const parsed = JSON.parse(raw) as unknown

    if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
      return parsed as Record<string, PuddingPluginOptions>
    }
  } catch {}

  return {}
}

function saveEnvOptions(key: string, options: PuddingPluginOptions): void {
  const map = readEnvOptionsMap()
  map[key] = options
  process.env[OPTIONS_ENV] = JSON.stringify(map)
}

function stateFor(root: string, name: string): PluginState {
  const resolvedRoot = resolve(root)
  const key = stateKey(resolvedRoot, name)
  let state = states.get(key)

  if (!state && name) {
    const fallback = states.get(stateKey(resolvedRoot, ''))
    if (fallback) return fallback
  }

  if (!state) {
    const envMap = readEnvOptionsMap()
    const options = envMap[key] ?? (name ? envMap[stateKey(resolvedRoot, '')] : undefined) ?? {}
    state = { root: resolvedRoot, name, options, changed: new Set() }
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
  name?: string
  config?: { root?: string; name?: string | { label: string } }
  provide(key: string, value: unknown): void
  onTestsRerun?(
    cb: (
      specs: readonly (
        | string
        | {
            moduleId?: string
            project?: {
              name?: string
              config?: { root?: string; name?: string | { label: string } }
            }
          }
      )[],
    ) => void | Promise<void>,
  ): void
}

interface VitestConfigLike {
  root?: string
  test?: {
    name?: string | { label: string }
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

export function pudding(options: PuddingPluginOptions = {}): {
  name: string
  config(userConfig: VitestConfigLike): VitestConfigLike
  configureServer(server: ViteServerLike): void
} {
  const setupFile = fileURLToPath(import.meta.url)
  const lawInclude = options.lawInclude ?? DEFAULT_LAW_INCLUDE
  const { lawInclude: _ignored, ...runOptions } = options

  return {
    name: 'pudding',
    config(userConfig) {
      const root = resolve(userConfig.root ?? process.cwd())
      const name = projectNameOf(userConfig.test?.name)
      const key = stateKey(root, name)
      states.set(key, { root, name, options: runOptions, changed: new Set() })
      saveEnvOptions(key, runOptions)

      const hasInclude = userConfig.test?.include !== undefined
      const existingInclude = userConfig.test?.include ?? DEFAULT_VITEST_INCLUDE
      const addedInclude = hasInclude
        ? lawInclude.filter((p) => !existingInclude.includes(p))
        : [...new Set([...DEFAULT_VITEST_INCLUDE, ...lawInclude])]
      const existingSetup = userConfig.test?.globalSetup
      const setups = Array.isArray(existingSetup)
        ? existingSetup
        : existingSetup
          ? [existingSetup]
          : []
      return {
        test: {
          ...(addedInclude.length ? { include: addedInclude } : {}),
          ...(setups.includes(setupFile) ? {} : { globalSetup: [setupFile] }),
        },
      }
    },
    configureServer(server) {
      const serverRoot = resolve(server.config?.root ?? process.cwd())

      const recordChange = (file: string) => {
        const resolvedFile = resolve(file)
        let matched = false

        for (const state of states.values()) {
          if (
            state.root === serverRoot ||
            resolvedFile.startsWith(state.root + sep) ||
            resolvedFile === state.root
          ) {
            state.changed.add(resolvedFile)
            matched = true
          }
        }

        if (!matched) stateFor(serverRoot, '').changed.add(resolvedFile)
      }

      server.watcher?.on('change', recordChange)
      server.watcher?.on('add', recordChange)
      server.watcher?.on('unlink', recordChange)
    },
  }
}

export async function setup(project: GlobalSetupProject): Promise<() => void> {
  const root = resolve(project.config?.root ?? process.cwd())
  const name = projectNameOf(project.name ?? project.config?.name)
  const state = stateFor(root, name)
  const key = stateKey(state.root, state.name)
  const session = createWatchSession()
  state.session = session

  const dir = mkdtempSync(join(tmpdir(), 'pudding-vitest-'))
  const reportFile = join(dir, 'report.json')

  const cleanup = () => {
    session.close()
    states.delete(key)
    rmSync(dir, { recursive: true, force: true })
  }

  const snapshot: PrecomputedReport = { root, errors: [], lawsByFile: {}, runs: 0 }

  const applyReport = (
    report: Awaited<ReturnType<typeof run>>,
    replacedFiles?: readonly string[],
  ) => {
    snapshot.runs++

    if (
      !replacedFiles &&
      report.errors.length === 1 &&
      report.errors[0] === 'no law files were found'
    ) {
      snapshot.errors = []
      snapshot.lawsByFile = {}
      writeSnapshot(reportFile, snapshot)
      return
    }

    snapshot.errors = report.errors

    if (!replacedFiles) snapshot.lawsByFile = {}
    else for (const file of replacedFiles) delete snapshot.lawsByFile[resolve(file)]

    for (const entry of report.laws) {
      const fileKey = resolve(entry.file)
      const list = snapshot.lawsByFile[fileKey] ?? []
      list.push(entry)
      snapshot.lawsByFile[fileKey] = list
    }

    writeSnapshot(reportFile, snapshot)
  }

  try {
    const initial = await run({ ...state.options, cwd: root, session })
    applyReport(initial)
  } catch (error) {
    cleanup()
    throw error
  }

  project.provide('puddingReportFile', reportFile)

  project.onTestsRerun?.(async (specs) => {
    const changed = [...state.changed]
    state.changed.clear()
    const rerunLawFiles = new Set<string>()

    for (const spec of specs) {
      if (typeof spec === 'object' && spec?.project) {
        const specName = projectNameOf(spec.project.name ?? spec.project.config?.name)
        const specRoot = spec.project.config?.root ? resolve(spec.project.config.root) : root
        if (spec.project !== project && (specName !== name || specRoot !== root)) continue
      }

      const id = typeof spec === 'string' ? spec : spec?.moduleId
      if (id && isLawPath(id) && existsSync(id)) rerunLawFiles.add(resolve(id))
    }

    let needFull = false

    for (const file of changed) {
      if (file.endsWith('.json') || /pudding\.config\./.test(file) || !existsSync(file)) {
        needFull = true
        break
      }

      const affected = session.affected(file)

      if (!affected) {
        needFull = true
        break
      }

      for (const lawFile of affected) if (existsSync(lawFile)) rerunLawFiles.add(resolve(lawFile))
    }

    if (needFull) {
      session.close()
      const next = await run({ ...state.options, cwd: root, session })
      applyReport(next)
      return
    }

    if (!rerunLawFiles.size) return
    const lawFiles = [...rerunLawFiles].sort()
    const next = await run({
      ...state.options,
      cwd: root,
      session,
      lawFiles,
      ...(changed.length ? { changedFiles: changed } : {}),
    })
    applyReport(next, lawFiles)
  })

  return cleanup
}
