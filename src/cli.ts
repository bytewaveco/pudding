#!/usr/bin/env node
import { readFileSync, watch as watchFiles } from "node:fs"
import { dirname, join, resolve } from "node:path"
import { fileURLToPath } from "node:url"
import { parseArgs } from "node:util"
import { createInterface } from "node:readline/promises"
import { installLean, LEAN_VERSION } from "./install.ts"
import { format, type Reporter } from "./report.ts"
import { LeanMissing, run, type RunOptions } from "./runner.ts"

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

const REPORTERS = ["default", "verbose", "json", "github"]
const IGNORED = /(^|[\\/])(node_modules|\.git|dist|\.pudding|\.toolchain|\.lab)([\\/]|$)/

async function main(): Promise<void> {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      name: { type: "string", short: "t" }, watch: { type: "boolean", short: "w" }, strict: { type: "boolean" },
      reporter: { type: "string" }, "no-cache": { type: "boolean" }, "no-cross-check": { type: "boolean" }, emit: { type: "string" },
      cwd: { type: "string" }, full: { type: "boolean" }, local: { type: "boolean" }, version: { type: "boolean", short: "v" }, help: { type: "boolean", short: "h" },
      // Kept so earlier invocations still work.
      json: { type: "boolean" }, verbose: { type: "boolean" },
    },
  })
  const cwd = resolve(values.cwd ?? process.cwd())
  if (values.help) return void process.stdout.write(HELP)
  if (values.version) {
    const manifest = JSON.parse(readFileSync(join(dirname(dirname(fileURLToPath(import.meta.url))), "package.json"), "utf8")) as { version: string }
    return void console.log(manifest.version)
  }
  if (positionals[0] === "install-lean") {
    return void (await installLean(cwd, { full: !!values.full, local: !!values.local, log: line => console.log(line) }))
  }

  const watching = values.watch || positionals[0] === "watch"
  const filters = positionals[0] === "watch" ? positionals.slice(1) : positionals
  const named = values.reporter ?? (values.json ? "json" : values.verbose ? "verbose" : undefined)
  if (named !== undefined && !REPORTERS.includes(named)) throw new Error(`unknown reporter \`${named}\`; choose one of ${REPORTERS.join(", ")}`)
  const options: RunOptions = {
    cwd,
    ...(filters.length ? { files: filters } : {}),
    ...(values.name ? { name: values.name } : {}),
    ...(values.strict ? { strict: true } : {}),
    ...(values["no-cache"] ? { cache: false } : {}),
    ...(values["no-cross-check"] ? { crossCheck: false } : {}),
    ...(values.emit ? { emit: values.emit } : {}),
  }
  const once = async () => {
    const report = await run(options)
    const reporter = (named ?? report.reporter ?? (process.env["GITHUB_ACTIONS"] ? "github" : "default")) as Reporter
    process.stdout.write(format(report, { cwd, color: process.stdout.isTTY === true && reporter !== "json", reporter }))
    return report.ok
  }
  if (!watching) return once().then(ok => void (process.exitCode = ok ? 0 : 1))
  return watch(cwd, once)
}

/** Check, then check again after each change to a source file, until interrupted. */
async function watch(cwd: string, once: () => Promise<boolean>): Promise<void> {
  let running = false
  let again = false
  let timer: NodeJS.Timeout | undefined
  const interactive = process.stdout.isTTY === true
  const cycle = async () => {
    if (running) return void (again = true)
    running = true
    do {
      again = false
      if (interactive) process.stdout.write("\x1b[2J\x1b[3J\x1b[H")
      try {
        await once()
      } catch (error) {
        process.stderr.write(`pudding: ${error instanceof Error ? error.message : String(error)}\n`)
      }
      process.stdout.write(interactive ? "\n  Watching for changes. Press q to quit, enter to check again.\n" : "\n  Watching for changes.\n")
    } while (again)
    running = false
  }
  watchFiles(cwd, { recursive: true }, (_event, file) => {
    if (!file || IGNORED.test(file) || !/\.(m?ts|cts|json)$/.test(file)) return
    clearTimeout(timer)
    timer = setTimeout(() => void cycle(), 60)
  })
  if (process.stdin.isTTY) {
    process.stdin.setRawMode(true)
    process.stdin.resume()
    process.stdin.on("data", data => {
      const key = data.toString()
      if (key === "q" || key === "\x03") process.exit(0)
      if (key === "\r" || key === "\n") void cycle()
    })
  }
  await cycle()
}

/** Offer to download Lean when it is missing and someone is there to answer. */
async function offerInstall(): Promise<boolean> {
  if (!process.stdin.isTTY || !process.stdout.isTTY) return false
  const prompt = createInterface({ input: process.stdin, output: process.stdout })
  const answer = await prompt.question(`Lean ${LEAN_VERSION} is not installed. Download it now? [Y/n] `)
  prompt.close()
  if (answer.trim() !== "" && !/^y/i.test(answer.trim())) return false
  await installLean(process.cwd(), { full: false, local: false, log: line => console.log(line) })
  return true
}

try {
  await main()
} catch (error) {
  if (error instanceof LeanMissing && await offerInstall()) await main()
  else {
    process.stderr.write(`pudding: ${error instanceof Error ? error.message : String(error)}\n`)
    process.exitCode = 2
  }
}
