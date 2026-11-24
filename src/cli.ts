#!/usr/bin/env node
import { existsSync, readFileSync, watch as watchFiles } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import { createInterface } from 'node:readline/promises'
import { fileURLToPath } from 'node:url'
import { parseArgs } from 'node:util'

import { installLean, LEAN_VERSION } from './install.ts'
import { format, type Reporter } from './report.ts'
import { createWatchSession, LeanMissing, run, type RunOptions } from './runner.ts'

const HELP = `pudding: prove laws about TypeScript functions

Usage
  pudding [filters...] [options]   check law files; filters match parts of their paths
  pudding watch [filters...]       check again whenever a file changes
  pudding install-lean             download the Lean runtime

Options
  -t, --name <pattern>   only laws whose name matches this regular expression
  -w, --watch            same as the watch command
      --strict           fail when a law was only executed, not proved
      --reporter <name>  default, verbose, json or github
      --no-cache         ignore results from earlier runs
      --no-cross-check   do not execute laws against the real code
      --emit <file>      also write the generated Lean source to <file>
      --cwd <dir>        project directory (default: current directory)
      --full             with install-lean: keep the whole toolchain
      --local            with install-lean: install into ./.toolchain, not the shared cache
  -v, --version
  -h, --help
`

const REPORTERS = ['default', 'verbose', 'json', 'github']
const IGNORED = /(^|[\\/])(node_modules|\.git|dist|\.pudding|\.toolchain|\.lab)([\\/]|$)/

async function main(): Promise<void> {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      name: { type: 'string', short: 't' },
      watch: { type: 'boolean', short: 'w' },
      strict: { type: 'boolean' },
      reporter: { type: 'string' },
      'no-cache': { type: 'boolean' },
      'no-cross-check': { type: 'boolean' },
      emit: { type: 'string' },
      cwd: { type: 'string' },
      full: { type: 'boolean' },
      local: { type: 'boolean' },
      version: { type: 'boolean', short: 'v' },
      help: { type: 'boolean', short: 'h' },
      json: { type: 'boolean' },
      verbose: { type: 'boolean' },
    },
  })
  const cwd = resolve(values.cwd ?? process.cwd())
  if (values.help) return void process.stdout.write(HELP)

  if (values.version) {
    const manifest = JSON.parse(
      readFileSync(join(dirname(dirname(fileURLToPath(import.meta.url))), 'package.json'), 'utf8'),
    ) as { version: string }
    return void console.log(manifest.version)
  }

  if (positionals[0] === 'install-lean') {
    return void (await installLean(cwd, {
      full: !!values.full,
      local: !!values.local,
      log: (line) => console.log(line),
    }))
  }

  const watching = values.watch || positionals[0] === 'watch'
  const filters = positionals[0] === 'watch' ? positionals.slice(1) : positionals
  const named = values.reporter ?? (values.json ? 'json' : values.verbose ? 'verbose' : undefined)

  if (named !== undefined && !REPORTERS.includes(named))
    throw new Error(`unknown reporter \`${named}\`; choose one of ${REPORTERS.join(', ')}`)

  const options: RunOptions = {
    cwd,
    ...(filters.length ? { files: filters } : {}),
    ...(values.name ? { name: values.name } : {}),
    ...(values.strict ? { strict: true } : {}),
    ...(values['no-cache'] ? { cache: false } : {}),
    ...(values['no-cross-check'] ? { crossCheck: false } : {}),
    ...(values.emit ? { emit: values.emit } : {}),
  }

  const once = async (override?: Partial<RunOptions>) => {
    const report = await run({ ...options, ...override })
    const reporter = (named ??
      report.reporter ??
      (process.env['GITHUB_ACTIONS'] ? 'github' : 'default')) as Reporter
    process.stdout.write(
      format(report, {
        cwd,
        color: process.stdout.isTTY === true && reporter !== 'json',
        reporter,
      }),
    )
    return report.ok
  }

  if (!watching) return once().then((ok) => void (process.exitCode = ok ? 0 : 1))
  return watch(cwd, once)
}

async function watch(
  cwd: string,
  once: (override?: Partial<RunOptions>) => Promise<boolean>,
): Promise<void> {
  const session = createWatchSession()
  let running = false
  let again = false
  let pendingFiles: Set<string> | 'all' = 'all'
  let timer: NodeJS.Timeout | undefined
  const interactive = process.stdout.isTTY === true

  const cycle = async () => {
    if (running) return void (again = true)
    running = true

    do {
      again = false
      const target = pendingFiles
      pendingFiles = new Set()
      let lawFiles: string[] | undefined

      if (target !== 'all') {
        const hit = new Set<string>()
        let needAll = false

        for (const file of target) {
          const affected = session.affected(file)

          if (!affected) {
            needAll = true
            break
          }

          for (const lawFile of affected) hit.add(lawFile)
        }

        if (!needAll) {
          if (!hit.size) continue
          lawFiles = [...hit].sort()
        }
      }

      if (interactive) process.stdout.write('\x1b[2J\x1b[3J\x1b[H')
      if (!lawFiles) session.close()

      try {
        await once({
          session,
          ...(lawFiles
            ? { lawFiles, ...(target !== 'all' ? { changedFiles: [...target] } : {}) }
            : {}),
        })
      } catch (error) {
        process.stderr.write(`pudding: ${error instanceof Error ? error.message : String(error)}\n`)
      }

      process.stdout.write(
        interactive
          ? '\n  Watching for changes. Press q to quit, enter to check again.\n'
          : '\n  Watching for changes.\n',
      )
    } while (again)

    running = false
  }

  watchFiles(cwd, { recursive: true }, (event, file) => {
    if (!file || IGNORED.test(file) || !/\.(m?[jt]sx?|c[jt]s|json)$/.test(file)) return
    const full = resolve(cwd, file)
    const tracked = (session.affected(full)?.length ?? 0) > 0

    if (
      file.endsWith('.json') ||
      /pudding\.config\./.test(file) ||
      (event === 'rename' && (!existsSync(full) || !tracked)) ||
      (/\.law\.[mc]?[jt]sx?$/.test(file) && !tracked)
    ) {
      pendingFiles = 'all'
    } else if (pendingFiles !== 'all') pendingFiles.add(full)

    clearTimeout(timer)
    timer = setTimeout(() => void cycle(), 60)
  })

  const shutdown = () => {
    session.close()
    process.exit(0)
  }

  process.on('SIGINT', shutdown)
  process.on('SIGTERM', shutdown)

  if (process.stdin.isTTY) {
    process.stdin.setRawMode(true)
    process.stdin.resume()
    process.stdin.on('data', (data) => {
      const key = data.toString()
      if (key === 'q' || key === '\x03') shutdown()

      if (key === '\r' || key === '\n') {
        pendingFiles = 'all'
        void cycle()
      }
    })
  }

  await cycle()
}

async function offerInstall(): Promise<boolean> {
  if (!process.stdin.isTTY || !process.stdout.isTTY) return false
  const prompt = createInterface({ input: process.stdin, output: process.stdout })
  const answer = await prompt.question(
    `Lean ${LEAN_VERSION} is not installed. Download it now? [Y/n] `,
  )
  prompt.close()
  if (answer.trim() !== '' && !/^y/i.test(answer.trim())) return false
  await installLean(process.cwd(), { full: false, local: false, log: (line) => console.log(line) })
  return true
}

try {
  await main()
} catch (error) {
  if (error instanceof LeanMissing && (await offerInstall())) await main()
  else {
    process.stderr.write(`pudding: ${error instanceof Error ? error.message : String(error)}\n`)
    process.exitCode = 2
  }
}
