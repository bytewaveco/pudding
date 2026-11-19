#!/usr/bin/env node
import { parseArgs } from "node:util"
import { resolve } from "node:path"
import { installLean } from "./install.ts"
import { format } from "./report.ts"
import { run } from "./runner.ts"

const HELP = `pudding: prove laws about TypeScript functions

Usage
  pudding [options]        check every law file
  pudding install-lean     download the Lean toolchain into .toolchain/

Options
  --strict            fail when a law was only executed, not proved
  --no-cache          ignore results from earlier runs
  --no-cross-check    do not execute laws against the real code
  --emit <file>       also write the generated Lean source to <file>
  --json              print the report as JSON
  --verbose           list every law, not only the ones that need attention
  --cwd <dir>         project directory (default: current directory)
  --full              with install-lean: keep the whole toolchain
`

const { values, positionals } = parseArgs({
  allowPositionals: true,
  options: {
    strict: { type: "boolean" }, "no-cache": { type: "boolean" }, "no-cross-check": { type: "boolean" }, emit: { type: "string" },
    json: { type: "boolean" }, verbose: { type: "boolean" }, cwd: { type: "string" }, full: { type: "boolean" }, help: { type: "boolean", short: "h" },
  },
})
const cwd = resolve(values.cwd ?? process.cwd())

try {
  if (values.help) process.stdout.write(HELP)
  else if (positionals[0] === "install-lean") installLean(cwd, { full: !!values.full, log: line => console.log(line) })
  else if (positionals.length) {
    process.stderr.write(`unknown command \`${positionals[0]}\`\n\n${HELP}`)
    process.exitCode = 2
  } else {
    const report = await run({
      cwd,
      ...(values.strict ? { strict: true } : {}),
      ...(values["no-cache"] ? { cache: false } : {}),
      ...(values["no-cross-check"] ? { crossCheck: false } : {}),
      ...(values.emit ? { emit: values.emit } : {}),
    })
    process.stdout.write(values.json ? JSON.stringify(report, null, 2) + "\n" : format(report, { cwd, color: process.stdout.isTTY === true, verbose: !!values.verbose }))
    if (!report.ok) process.exitCode = 1
  }
} catch (error) {
  process.stderr.write(`pudding: ${error instanceof Error ? error.message : String(error)}\n`)
  process.exitCode = 2
}
