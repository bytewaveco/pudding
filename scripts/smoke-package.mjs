// Pack the library, install the tarball into an empty project, and check that
// it proves a law there. This is the path a user takes, which the unit tests
// (run from the repository) do not cover. The project brings the compiler, so
// each kind of project is tried: TypeScript 7, tsrs beside an older
// TypeScript, and no TypeScript 7 compiler at all.

import { execFileSync, spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { locateLean } from "../dist/runner.js"

const root = dirname(dirname(fileURLToPath(import.meta.url)))
const { devDependencies } = JSON.parse(readFileSync(join(root, "package.json"), "utf8"))
// npm refuses a TypeScript older than the one Pudding asks for unless the
// project says, as here, that its own version is the one to use.
const older = { devDependencies: { typescript: "6.0.3" }, overrides: { "@bytewaveco/pudding": { typescript: "$typescript" } } }
const projects = [
  { name: "typescript", install: [`typescript@${devDependencies.typescript}`], compiler: /^TypeScript 7\./ },
  { name: "tsrs", manifest: older, install: [`tsrs@${devDependencies.tsrs}`], compiler: /^tsrs / },
  { name: "none", manifest: older, install: [], error: /no TypeScript 7 compiler was found/ },
]
const work = mkdtempSync(join(tmpdir(), "pudding-smoke-"))
const problems = []
try {
  const tarball = execFileSync("npm", ["pack", "--silent", "--pack-destination", work], { cwd: root, encoding: "utf8" }).trim().split("\n").at(-1)
  const lean = locateLean({}, root)
  for (const { name, manifest, install, compiler, error } of projects) {
    const project = join(work, name)
    mkdirSync(join(project, "src"), { recursive: true })
    writeFileSync(join(project, "package.json"), JSON.stringify({ name: "smoke", private: true, type: "module", ...manifest }))
    execFileSync("npm", ["install", "--silent", "--no-audit", "--no-fund", join(work, tarball), ...install], { cwd: project, stdio: "inherit" })
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
    const { PUDDING_COMPILER: _, ...env } = process.env
    const result = spawnSync("npx", ["pudding", "--reporter", "json"], { cwd: project, encoding: "utf8", env: { ...env, PUDDING_LEAN: lean } })
    if (!result.stdout.trim().startsWith("{")) throw new Error(`pudding printed no report in the ${name} project (exit ${result.status}):\n${result.stdout}\n${result.stderr}`)
    const report = JSON.parse(result.stdout)
    const fail = message => problems.push(`${name} project: ${message}`)
    if (error) {
      if (report.errors.length !== 1 || !error.test(report.errors[0])) fail(`errors were ${JSON.stringify(report.errors)}`)
      if (report.laws.length) fail("laws were checked without a compiler")
      continue
    }
    const statuses = Object.fromEntries(report.laws.map(entry => [entry.name, entry.status]))
    const expected = { "the order of two items does not matter": "proved", "FALSE: quantity is ignored": "failed" }
    if (JSON.stringify(statuses) !== JSON.stringify(expected)) fail(`statuses were ${JSON.stringify(statuses)}`)
    if (report.errors.length || report.warnings.length) fail(`errors ${JSON.stringify(report.errors)}, warnings ${JSON.stringify(report.warnings)}`)
    if (!compiler.test(report.compiler)) fail(`the compiler was ${JSON.stringify(report.compiler)}`)
    if (result.status !== 1) fail(`exit code was ${result.status}, expected 1 because one law is false`)
  }
  if (problems.length) {
    console.error("package smoke test failed:\n  " + problems.join("\n  "))
    process.exitCode = 1
  } else console.log(`package smoke test passed: ${tarball} installs and proves laws in fresh projects with ${projects.filter(project => project.compiler).map(project => project.name).join(" and ")}`)
} finally {
  rmSync(work, { recursive: true, force: true })
}
