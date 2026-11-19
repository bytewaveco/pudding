// Pack the library, install the tarball into an empty project, and check that
// it proves a law there. This is the path a user takes, which the unit tests
// (run from the repository) do not cover.

import { execFileSync, spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { locateLean } from "../dist/runner.js"

const root = dirname(dirname(fileURLToPath(import.meta.url)))
const work = mkdtempSync(join(tmpdir(), "pudding-smoke-"))
try {
  const tarball = execFileSync("npm", ["pack", "--silent", "--pack-destination", work], { cwd: root, encoding: "utf8" }).trim().split("\n").at(-1)
  const project = join(work, "project")
  mkdirSync(join(project, "src"), { recursive: true })
  writeFileSync(join(project, "package.json"), JSON.stringify({ name: "smoke", private: true, type: "module" }))
  execFileSync("npm", ["install", "--silent", "--no-audit", "--no-fund", join(work, tarball)], { cwd: project, stdio: "inherit" })
  // Bundler-style source: no file extension on the import, and a type imported without `type`.
  writeFileSync(join(project, "src", "cart.ts"), `export interface Item { price: bigint; quantity: bigint }
export function subtotal(items: readonly Item[]): bigint {
  let sum = 0n
  for (const item of items) sum += item.price * item.quantity
  return sum
}
`)
  writeFileSync(join(project, "src", "cart.law.ts"), `import { domain, expect, law } from "@bytewaveco/pudding"
import { Item, subtotal } from "./cart"

law("the order of two items does not matter", domain<[Item, Item]>(), ([a, b]) => {
  expect(subtotal([a, b])).toEqual(subtotal([b, a]))
})

law("FALSE: quantity is ignored", domain<Item>(), item => {
  expect(subtotal([item])).toEqual(item.price)
})
`)
  const lean = locateLean({}, root)
  const result = spawnSync("npx", ["pudding", "--reporter", "json"], { cwd: project, encoding: "utf8", env: { ...process.env, PUDDING_LEAN: lean } })
  if (!result.stdout.trim().startsWith("{")) throw new Error(`pudding printed no report (exit ${result.status}):\n${result.stdout}\n${result.stderr}`)
  const report = JSON.parse(result.stdout)
  const statuses = Object.fromEntries(report.laws.map(entry => [entry.name, entry.status]))
  const expected = { "the order of two items does not matter": "proved", "FALSE: quantity is ignored": "failed" }
  const problems = []
  if (JSON.stringify(statuses) !== JSON.stringify(expected)) problems.push(`statuses were ${JSON.stringify(statuses)}`)
  if (report.errors.length || report.warnings.length) problems.push(`errors ${JSON.stringify(report.errors)}, warnings ${JSON.stringify(report.warnings)}`)
  if (result.status !== 1) problems.push(`exit code was ${result.status}, expected 1 because one law is false`)
  if (problems.length) {
    console.error("package smoke test failed:\n  " + problems.join("\n  "))
    process.exitCode = 1
  } else console.log(`package smoke test passed: ${tarball} installs and proves laws in a fresh project`)
} finally {
  rmSync(work, { recursive: true, force: true })
}
