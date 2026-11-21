import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { cpSync, existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { isAbsolute, join } from "node:path"
import { after, before, describe, test } from "node:test"
import * as ir from "../src/ir.ts"
import { checksFor, FAST_HEADER, prove } from "../dist/lean.js"
import { createWatchSession, locateLean, run, type Report } from "../dist/runner.js"
import { findInput, showInputs } from "../dist/search.js"

const fixtures = join(import.meta.dirname, "fixtures")
const lean = locateLean({}, join(import.meta.dirname, ".."))
// Every run here, and every Vitest it starts, uses that Lean and a proof log of its own.
// A Lean found only on the PATH is left to be found there again.
if (isAbsolute(lean)) process.env["PUDDING_LEAN"] = lean
const cacheDirectory = mkdtempSync(join(tmpdir(), "pudding-cache-"))
process.env["PUDDING_CACHE_DIR"] = cacheDirectory
after(() => rmSync(cacheDirectory, { recursive: true, force: true }))
const law = (report: Report, name: string) => {
  const found = report.laws.find(entry => entry.name === name)
  assert.ok(found, `no law named ${name}`)
  return found
}

describe("the suite project", () => {
  let report: Report
  before(async () => {
    report = await run({ cwd: join(fixtures, "suite"), cache: false })
  })

  test("reports no project-level errors", () => assert.deepEqual(report.errors, []))

  test("every law lands in the status its name announces", () => {
    assert.ok(report.laws.length >= 25)
    for (const entry of report.laws) assert.equal(entry.status, announced(entry.name), `${entry.name}: ${JSON.stringify(entry.findings)}`)
  })

  test("a false law comes with a concrete counterexample and both sides", () => {
    const [finding] = law(report, "FALSE: halving and doubling returns the input").findings
    assert.equal(finding?.kind, "counterexample")
    assert.deepEqual(finding?.inputs, { x: "1n" })
    assert.match(finding?.detail ?? "", /actual: +0n\nexpected: 1n/)
    assert.match(finding?.text ?? "", /^expect\(/)
  })

  test("inputs are named as the law names them, including object fields", () => {
    const [finding] = law(report, "FALSE: any order ships").findings
    assert.equal(finding?.kind, "throws")
    assert.deepEqual(Object.keys(finding?.inputs ?? {}).sort(), ["order.paid", "order.status"])
    assert.match(finding?.file ?? "", /orders\.ts$/)
  })

  test("division by an unguarded variable is reported as a possible throw", () => {
    const kinds = law(report, "FALSE: dividing by any number of parts is safe").findings.map(f => f.kind)
    assert.ok(kinds.includes("throws"))
  })

  test("expectations that can never be reached are rejected", () => {
    for (const name of ["VACUOUS: contradictory guard", "VACUOUS: contradictory arithmetic guard"]) {
      assert.deepEqual(law(report, name).findings.map(f => f.kind), ["vacuous"])
    }
  })

  test("a true law beyond the automation is unproved, and proved once a proof is supplied", () => {
    assert.deepEqual(law(report, "UNPROVED: a product of positives is positive").findings.map(f => f.kind), ["unproved"])
    assert.equal(law(report, "a product of positives is positive, with a supplied proof").status, "proved")
  })

  test("every alternative of a union input is covered", () => {
    const findings = law(report, "FALSE: scaling doubles the area").findings
    assert.deepEqual(findings.map(f => Object.keys(f.inputs ?? {}).join()), ["shape.side", "shape.width,shape.height"])
  })

  test("code outside the supported subset is executed instead and says so", () => {
    const sampled = law(report, "SAMPLED: the total of a pair is their sum")
    assert.match(sampled.notes[0] ?? "", /not proved: `\.copyWithin` .* \(fallback\.ts:3:10\)/)
    assert.equal(law(report, "FALSE when executed: totals ignore the first amount").findings[0]?.kind, "counterexample")
  })

  test("strict mode refuses laws that were only executed", async () => {
    const strict = await run({ cwd: join(fixtures, "suite"), cache: false, strict: true })
    assert.equal(law(strict, "CHECKED: initials are one character").status, "failed")
  })
})

/** The status a law's name announces: FALSE, VACUOUS and UNPROVED fail; SAMPLED and CHECKED fall back; the rest are proved. */
function announced(name: string) {
  const own = name.split(" > ").at(-1)!
  return /^(FALSE|VACUOUS|UNPROVED)/.test(own) ? "failed" : own.startsWith("SAMPLED") ? "sampled" : own.startsWith("CHECKED") ? "checked" : "proved"
}

describe("imperative code", () => {
  let report: Report
  before(async () => {
    report = await run({ cwd: join(fixtures, "language"), cache: false })
  })

  test("loops, reassignment, reduce and bigint text are proved or refuted as announced", () => {
    assert.deepEqual(report.errors, [])
    assert.ok(report.laws.length >= 30)
    for (const entry of report.laws) assert.equal(entry.status, announced(entry.name), `${entry.name}: ${JSON.stringify(entry.findings)}`)
  })

  test("the translated model never disagrees with the running code", () => {
    assert.deepEqual(report.laws.flatMap(entry => entry.findings).filter(f => f.kind === "mismatch"), [])
    assert.deepEqual(report.laws.flatMap(entry => entry.notes).filter(note => note.includes("not compared")), [])
  })

  test("a refuted loop comes with the inputs that break it", () => {
    const [finding] = law(report, "loops > FALSE: break keeps looking after the first match").findings
    assert.deepEqual(finding?.inputs, { a: "-1n", b: "-2n" })
  })

  test("expectations inside a helper are reported where they are written", () => {
    const findings = law(report, "helpers that assert > FALSE: the helper's bounds are too tight").findings
    assert.deepEqual(findings.map(f => f.line), [111, 112])
  })

  test("numbers are whole numbers: results that could stop being exact are reported", () => {
    const [grows] = law(report, "whole numbers > FALSE: adding one always grows a number").findings
    assert.equal(grows?.kind, "inexact")
    assert.deepEqual(grows?.inputs, { value: "9007199254740991" })
    const [zero] = law(report, "whole numbers > FALSE: pages never divide by zero").findings
    assert.equal(zero?.kind, "inexact")
    assert.deepEqual(zero?.inputs, { size: "0" })
    assert.match(law(report, "counted loops > SAMPLED: plain division is refused").notes[0] ?? "", /dividing numbers can give a fraction/)
  })

  test("a law is translated once per value of a small input that a loop bound depends on", () => {
    const entry = law(report, "counted loops > a loop bounded by a small input is unrolled for each of its values")
    assert.equal(entry.status, "proved")
    assert.ok(entry.cases >= 21, `covered ${entry.cases} cases`)
    assert.equal(law(report, "a while loop bounded by a small input").status, "proved")
  })

  test("what cannot be modeled exactly is refused by name", () => {
    const note = (name: string) => law(report, name).notes[0] ?? ""
    assert.match(note("SAMPLED: a closure that outlives the variable it assigns"), /uses `count`, a variable that is reassigned, after the function that declared it has returned/)
    assert.match(note("SAMPLED: assignment used as a value"), /assignment used as a value/)
    assert.match(note("counted loops > SAMPLED: a loop bounded by a large input cannot be unrolled"), /how many times this loop runs depends on a value that is not known here/)
  })
})

describe("grouping and selection", () => {
  const cwd = join(fixtures, "grouped")
  const statuses = (report: Report) => Object.fromEntries(report.laws.map(entry => [entry.name, entry.status]))

  test("describe prefixes names and scopes its declarations; skip, todo and only behave as in Vitest", async () => {
    const report = await run({ cwd, cache: false })
    assert.equal(report.ok, true)
    assert.deepEqual(statuses(report), {
      "three steps return to the start": "proved",
      "a single step > always changes the light": "proved",
      "a single step > stops only after amber": "proved",
      "a single step > from red > goes to green": "proved",
      "a single step > FALSE but skipped: never reaches amber": "skipped",
      "a single step > flashing amber": "todo",
      "a group that is switched off > FALSE but skipped: red is green": "skipped",
      "the one law that runs": "proved",
      "FALSE but not selected: red is terminal": "skipped",
    })
  })

  test("file and name filters narrow the run", async () => {
    const report = await run({ cwd, cache: false, files: ["lights"], name: "from red" })
    assert.deepEqual(report.laws.filter(entry => entry.status === "proved").map(entry => entry.name), ["a single step > from red > goes to green"])
    assert.ok(report.laws.every(entry => entry.file.endsWith("lights.law.ts")))
    const none = await run({ cwd, cache: false, files: ["no-such-file"] })
    assert.match(none.errors[0] ?? "", /no law file matches/)
  })

  test("a focused law narrows its file even when a name filter leaves it out", async () => {
    const report = await run({ cwd, cache: false, files: ["only"], name: "not selected" })
    assert.deepEqual(statuses(report), { "the one law that runs": "skipped", "FALSE but not selected: red is terminal": "skipped" })
  })

  test("the project needs no tsconfig of its own", () => {
    assert.equal(existsSync(join(cwd, "tsconfig.json")), false)
  })
})

describe("constructs that once produced a wrong proof", () => {
  // Every law in this fixture is false or throws when it runs. None may be
  // proved, with or without the execution that normally backs a proof up.
  for (const crossCheck of [true, false]) {
    test(`nothing is proved ${crossCheck ? "with" : "without"} executing the laws`, async () => {
      const report = await run({ cwd: join(fixtures, "soundness"), cache: false, crossCheck })
      assert.equal(report.laws.length, 55)
      // Two laws in merged.law.ts state the same functions correctly and must still be proved.
      for (const entry of report.laws) assert.equal(entry.status, entry.name.startsWith("FALSE") ? "failed" : "proved", `${entry.name}: ${JSON.stringify(entry.findings)}`)
      assert.equal(report.laws.filter(entry => entry.status === "proved").length, 2)
    })
  }

  // A table may be given to an installed package while its module loads only
  // when the table as a whole is `as const`. The words alone, on one field or
  // in a comment, used to be enough.
  for (const crossCheck of [true, false]) {
    test(`only a table that is \`as const\` as a whole is trusted with a package, ${crossCheck ? "with" : "without"} executing the laws`, async () => {
      const report = await run({ cwd: join(fixtures, "trust"), cache: false, crossCheck })
      assert.equal(report.laws.length, 6)
      for (const entry of report.laws) assert.equal(entry.status, entry.name.startsWith("FALSE") ? "failed" : "proved", `${entry.name}: ${JSON.stringify(entry.findings)}`)
      if (!crossCheck) {
        const refusals = report.laws.filter(entry => entry.status === "failed").map(entry => entry.findings[0]?.message ?? "")
        for (const [i, name] of ["field", "comment", "wrapped", "inner", "inner"].entries()) assert.match(refusals[i]!, new RegExp(`^\`${name}\` is handed to other code while its module loads`))
      }
    })
  }

  test("each is refused or refuted for the right reason", async () => {
    const report = await run({ cwd: join(fixtures, "soundness"), cache: false, crossCheck: false })
    const message = (name: string) => law(report, name).findings.map(f => f.message).join(" | ")
    assert.match(message("FALSE: the outer function supplies the result"), /the expectation does not hold/)
    assert.match(message("FALSE: reading the binding succeeds"), /`value` is read before its declaration has run/)
    assert.match(message("FALSE: the erased parameter takes the argument"), /the expectation does not hold/)
    assert.match(message("FALSE: the callback uses its default index"), /the expectation does not hold/)
    assert.match(message("FALSE: every flag is set"), /reads a property the object does not have/)
    assert.match(message("FALSE: the literal stores its tag"), /`__proto__`/)
    assert.match(message("FALSE: the initial flag survives configuration"), /`flags` is handed to other code while its module loads at line 36/)
    assert.match(message("FALSE: a flag dictionary is empty"), /allows any number of properties/)
    assert.match(message("FALSE: ready initializes to true"), /`flag` is read while its module is loading/)
  })

  test("an unfinished proof is rejected by name", async () => {
    const report = await run({ cwd: join(fixtures, "soundness"), cache: false, crossCheck: false, name: "every bigint is zero" })
    const entry = law(report, "FALSE: every bigint is zero")
    assert.equal(entry.status, "failed")
    assert.deepEqual(entry.findings[0]?.inputs, { n: "1n" })
  })

  test("values that only misbehave at one constant are found there", async () => {
    const report = await run({ cwd: join(fixtures, "soundness"), cache: false, crossCheck: false, files: ["state"] })
    for (const name of ["FALSE: an unset let is always assigned", "FALSE: the default never runs", "FALSE: a number in a list matches a bigint", "FALSE: a number case matches a bigint"]) {
      assert.deepEqual(law(report, name).findings[0]?.inputs, { n: "424242n" }, name)
    }
  })

  test("a law that cannot be read as written is an error, never a pass", async () => {
    for (const crossCheck of [true, false]) {
      const report = await run({ cwd: join(fixtures, "unreadable"), cache: false, crossCheck })
      assert.equal(report.ok, false)
      assert.ok(report.laws.length >= 4)
      for (const entry of report.laws) assert.equal(entry.status, "failed", entry.name)
      const messages = report.laws.flatMap(entry => entry.findings.map(f => f.message)).join(" | ")
      assert.match(messages, /only law\(\) and describe\(\) calls and declarations are allowed/)
      assert.match(messages, /a law callback must be an ordinary synchronous function/)
      assert.match(messages, /the callback's parameter must be plain/)
    }
  })

  test("assignments inside a switch or a conditional loop survive an enclosing if", async () => {
    const report = await run({ cwd: join(fixtures, "soundness"), cache: false, crossCheck: false, files: ["merged"] })
    assert.deepEqual(law(report, "FALSE: a discount never exceeds a tenth of the subtotal").findings[0]?.inputs, { member: "true", coupon: '"VIP20"', subtotal: "10n" })
    assert.deepEqual(law(report, "FALSE: VAT never exceeds a fifth of the price").findings[0]?.inputs, { country: '"DE"', express: "true", price: "0n" })
  })

  test("an expectation in a helper that is never reached fails the law", async () => {
    const report = await run({ cwd: join(fixtures, "soundness"), cache: false, crossCheck: false, files: ["helper"] })
    assert.deepEqual(law(report, "FALSE: a settled paid order owes nothing").findings.map(f => f.kind), ["vacuous"])
  })

  test("a module that replaces how arrays iterate is refused", async () => {
    for (const crossCheck of [true, false]) {
      const report = await run({ cwd: join(fixtures, "iterator"), cache: false, crossCheck })
      const entry = law(report, "FALSE: a sum of two values adds them")
      assert.equal(entry.status, "failed")
      // Executed, the law simply fails; unexecuted, it is refused because of the replacement.
      assert.match(JSON.stringify(entry.findings), crossCheck ? /the law fails when executed/ : /`Array` is modified/)
    }
  })

  test("a module that replaces a built-in loses the model of that built-in", async () => {
    const unchecked = await run({ cwd: join(fixtures, "patched"), cache: false, crossCheck: false })
    assert.match(law(unchecked, "FALSE: a magnitude is never negative").findings[0]?.message ?? "", /`Math` is modified at .*patched\.ts:3/)
    // With execution the law is run on a sample, which does not happen to include the one value that breaks it.
    const executed = await run({ cwd: join(fixtures, "patched"), cache: false })
    assert.equal(law(executed, "FALSE: a magnitude is never negative").status, "sampled")
  })

  test("a module that replaces how Maps and Sets answer loses the model of them", async () => {
    const report = await run({ cwd: join(fixtures, "collections"), cache: false, crossCheck: false })
    assert.match(law(report, "FALSE: a Map gives what was put into it").findings[0]?.message ?? "", /`Map` is modified at .*collections\.ts:2/)
    assert.match(law(report, "FALSE: a Set only has what was added").findings[0]?.message ?? "", /`Map` is modified/)
  })

  test("a prototype held under another name is not trusted to stay as it is", async () => {
    for (const crossCheck of [true, false]) {
      const report = await run({ cwd: join(fixtures, "prototype"), cache: false, crossCheck })
      const entry = law(report, "FALSE: a property the object does not have is undefined")
      assert.equal(entry.status, "failed")
      assert.match(JSON.stringify(entry.findings), crossCheck ? /the law fails when executed/ : /a prototype is modified, stored or handed on at .*prototype\.ts:2/)
    }
  })

  test("a built-in or a prototype changed without assigning to one of its properties is still seen", async () => {
    // A method called on a prototype itself, a getter defined on one, a built-in replaced, a prototype taken out by a pattern.
    // Also a prototype taken out by a pattern from wherever the built-in is, by a parameter, through the global object, or by a quoted name.
    const cases = [
      ["method", /a prototype is modified/], ["getter", /a prototype is modified/], ["replaced", /`Map` is modified/], ["destructured", /a prototype is modified/],
      ["pattern", /a prototype is modified/], ["nested", /a prototype is modified/], ["parameter", /a prototype is modified/], ["global", /a prototype is modified/],
      ["quoted", /a prototype is modified/], ["globalGet", /a prototype is modified/], ["computed", /a prototype is modified/],
    ] as const
    for (const [directory, reason] of cases) {
      const report = await run({ cwd: join(fixtures, "tampered", directory), cache: false, crossCheck: false })
      assert.equal(report.laws.length, 1)
      assert.equal(report.laws[0]!.status, "failed", directory)
      assert.match(report.laws[0]!.findings[0]?.message ?? "", reason, directory)
    }
  })

  test("without strictNullChecks a domain is not trusted to list undefined, so nothing over it is proved", async () => {
    const report = await run({ cwd: join(fixtures, "loose"), cache: false, crossCheck: false })
    assert.deepEqual(report.errors, [])
    for (const entry of report.laws) {
      assert.equal(entry.status, "failed", entry.name)
      assert.match(entry.findings[0]?.message ?? "", /without `strictNullChecks`/)
    }
    assert.equal(report.laws.length, 2)
  })

  test("a project that leaves `strict` to the compiler has strictNullChecks, and its domains are proved over", async () => {
    const report = await run({ cwd: join(fixtures, "defaulted"), cache: false, crossCheck: false })
    assert.deepEqual(report.errors, [])
    assert.equal(law(report, "a value that may be undefined gives a bigint").status, "proved")
    assert.equal(law(report, "FALSE: a value that may be undefined is itself").findings[0]?.kind, "counterexample")
  })

  test("a law whose inputs leave out part of its domain is never said to cover every input", async () => {
    const report = await run({ cwd: join(fixtures, "loose"), cache: false })
    assert.equal(law(report, "SAMPLED: a value that may be undefined is a bigint").status, "sampled")
    for (const entry of report.laws) assert.notEqual(entry.status, "checked", entry.name)
  })

  test("an input type that refers to itself is refused without stopping the run", async () => {
    const report = await run({ cwd: join(fixtures, "recursive"), cache: false })
    assert.deepEqual(report.errors, [])
    assert.match(JSON.stringify(law(report, "recursive type").findings), /refers to itself/)
    assert.equal(law(report, "an ordinary law in the same file").status, "proved")
  })

  test("an import that TypeScript and Node resolve to different files stops the run", async () => {
    for (const crossCheck of [true, false]) {
      const report = await run({ cwd: join(fixtures, "ambiguous"), cache: false, crossCheck })
      assert.equal(report.ok, false)
      assert.equal(report.laws.length, 0)
      assert.match(report.errors[0] ?? "", /both that file and subject\.ts exist/)
    }
  })

  test("a module that throws an error of its own while loading fails its laws", async () => {
    const report = await run({ cwd: join(fixtures, "throwing"), cache: false })
    assert.match(law(report, "FALSE: the module loads").findings.map(f => f.message).join(), /throws when it is loaded \(SyntaxError/)
  })

  test("a law file that throws when loaded fails its laws", async () => {
    const report = await run({ cwd: join(fixtures, "soundness"), cache: false, files: ["loading"] })
    assert.match(law(report, "FALSE: ready initializes to true").findings.map(f => f.message).join(" | "), /throws when it is loaded \(ReferenceError/)
  })
})

test("a model that disagrees with the running code is never reported as proved", async () => {
  const report = await run({ cwd: join(fixtures, "mismatch"), cache: false })
  const entry = law(report, "only admins write")
  assert.equal(report.ok, false)
  assert.equal(entry.status, "failed")
  assert.deepEqual(entry.findings.map(f => f.kind), ["mismatch"])
  assert.deepEqual(entry.findings[0]?.inputs, { role: '"basic"' })
})

test("a table that load-time code may change is not trusted; the law is executed instead", async () => {
  const report = await run({ cwd: join(fixtures, "loadtime"), cache: false })
  const entry = law(report, "everyone writes once the table is patched")
  assert.equal(entry.status, "checked")
  assert.match(entry.notes[0] ?? "", /shares its module with a statement that runs on load at line 8/)
})

test("TypeScript errors stop the run before anything is proved", async () => {
  const report = await run({ cwd: join(fixtures, "typeerror"), cache: false })
  assert.equal(report.ok, false)
  assert.equal(report.laws.length, 0)
  assert.match(report.errors.join("\n"), /jobs\.law\.ts:5:17 TS2345/)
})

describe("caching", () => {
  let directory: string
  before(() => {
    directory = mkdtempSync(join(fixtures, ".tmp-"))
    cpSync(join(fixtures, "suite", "tsconfig.json"), join(directory, "tsconfig.json"))
    for (const name of ["shapes.ts", "shapes.law.ts"]) cpSync(join(fixtures, "suite", name), join(directory, name))
  })
  after(() => rmSync(directory, { recursive: true, force: true }))

  test("proved theorems are remembered, and an edit reproves only what changed", async () => {
    const first = await run({ cwd: directory })
    assert.equal(first.cachedObligations, 0)

    // Lean is not asked again about what it already accepted; the false law's two rejected theorems are retried.
    const second = await run({ cwd: directory })
    assert.deepEqual(second.laws, first.laws)
    assert.equal(second.obligations - second.cachedObligations, 2)

    const file = join(directory, "shapes.law.ts")
    writeFileSync(file, readFileSync(file, "utf8") + `
law("a rectangle of height two has twice its width as area", domain<bigint>(), width => {
  expect(area({ kind: "rect", width, height: 2n })).toEqual(width + width)
})
`)
    const third = await run({ cwd: directory })
    assert.equal(third.laws.length, first.laws.length + 1)
    assert.equal(law(third, "a rectangle of height two has twice its width as area").status, "proved")
    assert.equal(third.obligations - third.cachedObligations, 3)
  })

  test("a theorem proved in one project is not proved again in another", async () => {
    const [first, second] = [mkdtempSync(join(fixtures, ".tmp-")), mkdtempSync(join(fixtures, ".tmp-"))]
    const log = mkdtempSync(join(tmpdir(), "pudding-cache-"))
    process.env["PUDDING_CACHE_DIR"] = log
    try {
      for (const project of [first, second]) {
        for (const name of ["tsconfig.json", "shapes.ts", "shapes.law.ts"]) cpSync(join(fixtures, "suite", name), join(project, name))
      }
      assert.equal((await run({ cwd: first })).cachedObligations, 0)
      assert.equal((await run({ cwd: second, cache: false })).cachedObligations, 0)
      const report = await run({ cwd: second })
      // Only the false law's two rejected theorems go to Lean.
      assert.equal(report.obligations - report.cachedObligations, 2)
    } finally {
      process.env["PUDDING_CACHE_DIR"] = cacheDirectory
      for (const directory of [first, second, log]) rmSync(directory, { recursive: true, force: true })
    }
  })

  test("a file that changes how an import resolves is seen at once", async () => {
    // A cached result must never outlive a change in what the law quantifies over.
    const project = mkdtempSync(join(fixtures, ".tmp-"))
    try {
      writeFileSync(join(project, "types.d.ts"), `export type Day = "Mon"\n`)
      writeFileSync(join(project, "subject.ts"), `import type { Day } from "./types.js"\nexport const monday = (day: Day) => day === "Mon"\n`)
      writeFileSync(join(project, "days.law.ts"), `import { domain, expect, law } from "@bytewaveco/pudding"
import type { Day } from "./types.js"
import { monday } from "./subject.ts"

law("every day is Monday", domain<Day>(), day => expect(monday(day)).toBe(true))
`)
      assert.equal(law(await run({ cwd: project }), "every day is Monday").status, "proved")
      writeFileSync(join(project, "types.ts"), `export type Day = "Mon" | "Tue"\n`)
      const after = law(await run({ cwd: project }), "every day is Monday")
      assert.equal(after.status, "failed")
      assert.deepEqual(after.findings[0]?.inputs, { day: '"Tue"' })
    } finally {
      rmSync(project, { recursive: true, force: true })
    }
  })
})

describe("the Lean encoding", () => {
  const values = [-101n, -100n, -7n, -3n, -1n, 0n, 1n, 2n, 3n, 7n, 100n, 101n]
  const x: ir.Binder = { name: "x0", label: "x", ty: "int", domain: values }
  const y: ir.Binder = { name: "x1", label: "y", ty: "int", domain: values.filter(v => v !== 0n) }
  const vx = ir.variable("x0", "int")
  const vy = ir.variable("x1", "int")

  /** A statement saying Lean computes `e` to what JavaScript computes, at every point of the grid. */
  function agreement(e: ir.Expr, binders: ir.Binder[]) {
    let claim = ir.TRUE
    const visit = (index: number, env: Map<string, ir.Scalar>) => {
      const binder = binders[index]
      if (binder) return binder.domain!.forEach(value => visit(index + 1, new Map(env).set(binder.name, value)))
      const at = ir.all([...env].map(([name, value]) => ir.eq(ir.variable(name, "int"), ir.lit(value))))
      claim = ir.and(claim, ir.or(ir.not(at), ir.eq(e, ir.lit(ir.evaluate(e, env)))))
    }
    visit(0, new Map())
    return checksFor(binders, ir.TRUE, claim, undefined).map(check => check.statement)
  }

  test("agrees with JavaScript on bigint division, remainder and comparison, including negatives", async () => {
    const statements = [
      ...[7n, -7n, 100n, 1n, -1n].flatMap(d => [agreement(ir.div(vx, ir.lit(d)), [x]), agreement(ir.mod(vx, ir.lit(d)), [x])]).flat(),
      ...[7n, -7n, 100n, 1n, -1n].flatMap(d => agreement(ir.fdiv(vx, ir.lit(d)), [x])),
      ...agreement(ir.fdiv(vx, vy), [x, y]),
      ...agreement(ir.div(vx, vy), [x, y]),
      ...agreement(ir.mod(vx, vy), [x, y]),
      ...agreement(ir.ite(ir.lt(vx, vy), ir.sub(vx, vy), ir.neg(ir.mul(vx, vy))), [x, y]),
      ...agreement(ir.ite(ir.le(vx, vy), ir.add(vx, vy), vx), [x, y]),
    ]
    const outcomes = await prove(lean, FAST_HEADER, statements)
    assert.deepEqual(outcomes.filter(o => !o.ok).map(o => o.message.slice(0, 300)), [])
  })

  test("prints a bigint as JavaScript does", async () => {
    const wide: ir.Binder = { ...x, domain: [...values, 10n ** 30n, -(10n ** 30n) - 1n] }
    const outcomes = await prove(lean, FAST_HEADER, agreement(ir.concat(ir.toStr(vx), ir.lit("!")), [wide]))
    assert.deepEqual(outcomes.filter(o => !o.ok).map(o => o.message.slice(0, 300)), [])
  })

  test("every rejected theorem is seen, however many there are", async () => {
    // Lean stops reporting after 100 errors by default. A theorem it stayed silent about must not count as proved.
    const wrong = Array.from({ length: 150 }, (_, i) => ` : ((${i} : Int) == (${i + 1} : Int)) = true := by decide +kernel`)
    const outcomes = await prove(lean, FAST_HEADER, [...wrong, " : ((7 : Int) == (7 : Int)) = true := by decide +kernel"], 1)
    assert.equal(outcomes.filter(o => !o.ok).length, 150)
    assert.equal(outcomes.at(-1)?.ok, true)
  })

  test("rejects a wrong claim about division, so the agreement test can fail", async () => {
    const wrong = checksFor([x], ir.TRUE, ir.eq(ir.div(vx, ir.lit(2n)), ir.lit(-4n)), undefined).map(c => c.statement)
    const [outcome] = await prove(lean, FAST_HEADER, wrong)
    assert.equal(outcome?.ok, false)
  })
})

test("Vitest runs a law file as tests that report the proofs", () => {
  const root = join(fixtures, "vitest")
  const output = join(mkdtempSync(join(tmpdir(), "pudding-vitest-")), "report.json")
  const result = spawnSync("npx", ["vitest", "run", "--root", root, "--reporter", "json", "--outputFile", output], { encoding: "utf8", cwd: join(import.meta.dirname, "..") })
  const report = JSON.parse(readFileSync(output, "utf8")) as {
    numPassedTests: number; numFailedTests: number; numPendingTests: number; numTodoTests: number
    testResults: { assertionResults: { fullName: string; status: string; failureMessages: string[] }[] }[]
  }
  assert.deepEqual([report.numPassedTests, report.numFailedTests, report.numPendingTests, report.numTodoTests], [3, 1, 1, 1])
  const failed = report.testResults.flatMap(file => file.assertionResults).find(test => test.status === "failed")
  assert.equal(failed?.fullName, "parity FALSE: every face is even")
  assert.match(failed?.failureMessages.join("\n") ?? "", /the expectation does not hold[\s\S]*with face = 1[\s\S]*dice\.law\.ts:14:5/)
  assert.equal(result.status, 1)
})

test("DAG sharing proves repeated-division loops, while expressions past the size limit are still refused quickly", async () => {
  const report = await run({ cwd: join(fixtures, "growth"), cache: false })
  assert.equal(law(report, "settling never grows the value").status, "proved")
  const entry = law(report, "huge loop still stays above its input for positives")
  assert.equal(entry.status, "sampled")
  assert.match(entry.notes.join("\n"), /too large to check/)
  assert.ok(report.durationMs < 20_000, `took ${report.durationMs} ms`)
})

test("objects changed in place: aliases, early exits and evaluation order follow JavaScript", async () => {
  const report = await run({ cwd: join(fixtures, "mutation"), cache: false })
  assert.deepEqual(report.errors, [])
  assert.deepEqual(report.warnings, [])
  assert.ok(report.laws.length >= 40)
  for (const entry of report.laws) {
    const name = entry.name.split(" > ").at(-1)!
    // A refused law is executed instead, so it is never proved and never fails here.
    const expected = name.startsWith("FALSE") ? ["failed"] : name.startsWith("REFUSED") ? ["checked", "sampled"] : ["proved"]
    assert.ok(expected.includes(entry.status), `${entry.name}: ${entry.status} ${JSON.stringify(entry.findings)} ${entry.notes.join(" ")}`)
  }
  const note = (name: string) => law(report, name).notes[0] ?? ""
  assert.match(note("REFUSED: changing an input in place"), /one of the law's inputs, a shared constant/)
  assert.match(note("REFUSED: changing a module constant"), /one of the law's inputs, a shared constant/)
  assert.match(note("REFUSED: an object that may be either of two is no longer changed"), /a condition choosing between two objects/)
  assert.match(note("REFUSED: a push on one side of a condition that is not known"), /changes length on only one side of a condition/)
  assert.match(note("REFUSED: a change on the right of &&"), /the right side of `&&` changes an object in place/)
  assert.match(note("REFUSED: a change inside a callback of some"), /a callback of `\.some` changes an object in place/)
  assert.match(note("REFUSED: an object stored inside itself"), /inside itself/)
})

test("objects changed in place: no false law is proved by the model alone", async () => {
  // Without the cross-check nothing is executed, so this is what the translation itself claims.
  const report = await run({ cwd: join(fixtures, "mutation"), cache: false, crossCheck: false })
  for (const entry of report.laws) {
    const name = entry.name.split(" > ").at(-1)!
    if (name.startsWith("FALSE") || name.startsWith("REFUSED")) assert.equal(entry.status, "failed", entry.name)
    else assert.equal(entry.status, "proved", `${entry.name}: ${JSON.stringify(entry.findings)}`)
  }
})

describe("everyday idioms: undefined, defaults, rounding, lists, Maps and running totals", () => {
  // Each construct has a law that states it correctly and one that states it
  // wrongly. The wrong ones must fail on the model alone, without executing.
  for (const crossCheck of [true, false]) {
    test(`every law lands in the status its name announces, ${crossCheck ? "with" : "without"} executing the laws`, async () => {
      const report = await run({ cwd: join(fixtures, "idioms"), cache: false, crossCheck })
      assert.deepEqual(report.errors, [])
      assert.ok(report.laws.length >= 50)
      for (const entry of report.laws) {
        const expected = announced(entry.name)
        // Without executing, a law that is refused has nothing behind it and fails.
        assert.equal(entry.status, crossCheck || expected === "proved" ? expected : "failed", `${entry.name}: ${JSON.stringify(entry.findings)}`)
        // A false law has to be refuted by the model, not just refused by it, unless its name says it is only caught when executed.
        const own = entry.name.split(" > ").at(-1)!
        // A refutation names an input: a counterexample, a throw that is reached, or a number or lookup the model does not cover.
        if (!crossCheck && own.startsWith("FALSE:")) {
          assert.ok(entry.findings.length > 0 && entry.findings.every(f => f.kind === "counterexample" || f.kind === "throws" || f.kind === "inexact"), `${entry.name}: ${JSON.stringify(entry.findings)}`)
        }
      }
      assert.deepEqual(report.laws.flatMap(entry => entry.findings).filter(f => f.kind === "mismatch"), [])
    })
  }

  test("what is refused, and what throws, is named", async () => {
    const report = await run({ cwd: join(fixtures, "idioms"), cache: false })
    const note = (name: string) => law(report, name).notes[0] ?? ""
    const finding = (name: string) => law(report, name).findings[0]
    assert.match(note("callbacks with a running total > SAMPLED: a callback of .some that updates a variable"), /a callback of `\.some` assigns to a variable outside it/)
    assert.match(note("callbacks with a running total > SAMPLED: a closure that outlives the variable it updates"), /after the function that declared it has returned/)
    assert.match(note("callbacks with a running total > SAMPLED: an update on the right side of &&"), /the right side of `&&` assigns to a variable outside it/)
    assert.match(note("lists > SAMPLED: sorting by keys that are not known"), /sorting is supported where the order of the elements is known here/)
    assert.match(note("Map and Set > SAMPLED: a callback that uses the variable of a for loop around it"), /uses `i`, the variable of a `for` loop around it/)
    assert.equal(finding("values that may be undefined > FALSE: there is always a second node")?.kind, "throws")
    assert.match(finding("values that may be undefined > FALSE: what follows a ?. never throws")?.message ?? "", /reads a property of undefined/)
    assert.deepEqual(finding("rounding > FALSE: a half rounds away from zero")?.inputs, { n: "-1" })
    assert.equal(finding("rounding > FALSE: any whole number rounds exactly")?.kind, "inexact")
    assert.equal(finding("lists > FALSE: a callback that throws gives an answer")?.kind, "throws")
    assert.match(JSON.stringify(law(report, "values that may be undefined > FALSE: any key at all reads as undefined").findings), /every object inherits/)
  })
})

test("padStart and padEnd follow JavaScript for known strings and the text of whole numbers", async () => {
  const report = await run({ cwd: join(fixtures, "padding"), cache: false })
  assert.deepEqual(report.errors, [])
  assert.deepEqual(report.warnings, [])
  for (const entry of report.laws) {
    const expected = entry.name.startsWith("FALSE") ? ["failed"] : entry.name.startsWith("REFUSED") ? ["checked", "sampled"] : ["proved"]
    assert.ok(expected.includes(entry.status), `${entry.name}: ${entry.status} ${JSON.stringify(entry.findings)} ${entry.notes.join(" ")}`)
  }
  assert.match(law(report, "REFUSED: padding a string whose length is not known").notes[0] ?? "", /the length of this string is not known/)
})

test("strings too long for Lean to compare are refused, never called false", async () => {
  // Lean's kernel ran out of depth on these after many seconds, and the true law was reported as failed.
  const report = await run({ cwd: join(fixtures, "strings"), cache: false })
  const long = law(report, "a long banner reads the same however the marker was chosen")
  assert.equal(long.status, "checked")
  assert.match(long.notes.join("\n"), /too large to check/)
  assert.equal(law(report, "FALSE: a long banner ignores which marker was asked for").status, "failed")
  assert.equal(law(report, "a short banner is proved").status, "proved")
  assert.ok(report.durationMs < 10_000, `took ${report.durationMs} ms`)
})

describe("proof scripts", () => {
  test("a script can only be a proof of its own theorem", async () => {
    const report = await run({ cwd: join(fixtures, "scripts"), cache: false })
    for (const entry of report.laws) {
      const expected = /^(REJECTED|FALSE)/.test(entry.name) ? "failed" : "proved"
      assert.equal(entry.status, expected, `${entry.name}: ${JSON.stringify(entry.findings)}`)
    }
    // The law after the tampering script is refuted on its merits, so the script changed nothing for it.
    assert.equal(law(report, "FALSE: a law after the tampering script").findings[0]?.kind, "counterexample")
    assert.match(law(report, "REJECTED: a script that closes its own parentheses").findings[0]?.message ?? "", /parentheses in the proof script do not balance/)
    assert.match(law(report, "REJECTED: a script that hides a parenthesis in a comment").findings[0]?.message ?? "", /parentheses in the proof script do not balance/)
    assert.match(law(report, "REJECTED: a script that carries on past its proof").findings[0]?.message ?? "", /may not contain `macro_rules`/)
    assert.equal(law(report, "a true law with comments, nested block comments, strings and primed names").status, "proved")
  })

  test("proof script lexer handles Lean comments, literals, delimiters and commands accurately", async () => {
    const { scriptProblem } = await import("../dist/lean.js")
    assert.equal(scriptProblem("intro h'; simp_all -- ok )"), undefined)
    assert.equal(scriptProblem("/- outer /- inner ) -/ still -/ simp"), undefined)
    assert.equal(scriptProblem('have _ := "a\\")b"; simp'), undefined)
    assert.equal(scriptProblem('have _ := r#"a")b"#; simp'), undefined)
    assert.equal(scriptProblem("have _ := ')'; have _ := '\\''; simp"), undefined)
    assert.equal(scriptProblem("have «x)y» : True := trivial; exact «x)y»"), undefined)
    assert.match(scriptProblem("   -- only a comment\n/- and block -/") ?? "", /empty/)
    assert.match(scriptProblem("/- outer /- inner -/ unclosed") ?? "", /unterminated block comment/)
    assert.match(scriptProblem('have _ := "unclosed') ?? "", /unterminated string/)
    assert.match(scriptProblem("have _ := 'unclosed") ?? "", /unterminated character/)
    assert.match(scriptProblem("have _ := «unclosed") ?? "", /unterminated «quoted name»/)
    assert.match(scriptProblem('have _ := s!"{1 + 2}"') ?? "", /interpolated strings/)
    assert.match(scriptProblem("#eval 1; simp") ?? "", /Lean commands/)
    assert.match(scriptProblem("def bad := 1; simp") ?? "", /may not contain `def`/)
    assert.match(scriptProblem("simp [a, b") ?? "", /delimiters .* do not balance/)
    assert.match(scriptProblem("simp (a]") ?? "", /parentheses .* do not balance/)
  })

  test("a script that rests on anything but the standard axioms is rejected", async () => {
    const statement = (script: string) => ` : (((2 : Int) + 2) == 4) = true := by (\n  ${script}\n)`
    const [kernel, compiler, unfinished] = await prove(lean, FAST_HEADER, [statement("decide"), statement("native_decide"), statement("sorry")], undefined, true)
    assert.equal(kernel?.ok, true)
    assert.equal(compiler?.ok, false)
    assert.match(compiler?.message ?? "", /which Pudding does not accept/)
    assert.equal(unfinished?.ok, false)
    assert.match(unfinished?.message ?? "", /unfinished/)
  })

  test("a script that defines things after its proof cannot change another theorem in the same file", async () => {
    // Not how Pudding runs scripts (each gets its own file), but the reason it does.
    const tampering = " (x : Int) : (x == x) = true := by (\n  simp\n  macro_rules | `($a == $b) => `(true)\n)"
    const victim = " (x : Int) : (x == x + 1) = true := by rfl"
    const together = await prove(lean, FAST_HEADER, [tampering, victim], 1)
    assert.equal(together[0]?.ok, false)
    const apart = await prove(lean, FAST_HEADER, [tampering, victim], undefined, true)
    assert.deepEqual(apart.map(outcome => outcome.ok), [false, false])
  })
})

test("random programs: a true law is proved or refused, a false one is never proved", () => {
  // A small fixed sample of the differential fuzzer (scripts/fuzz.mjs), with and without executing the laws.
  for (const extra of [[], ["--cross-check"], ["--unbounded"]]) {
    const result = spawnSync("node", [join(import.meta.dirname, "..", "scripts", "fuzz.mjs"), "--seed", "7", "--programs", "80", "--batch", "40", "--quiet", ...extra], { encoding: "utf8" })
    assert.equal(result.status, 0, result.stdout + result.stderr)
    assert.match(result.stdout, /WRONG PROOFS\s+0/)
  }
})

describe("simplification", () => {
  const a = ir.variable("a", "int")
  test("groups string concatenation the same way however it was written", () => {
    const s = ir.variable("s", "str")
    const left = ir.concat(ir.concat(s, ir.lit("level:")), ir.concat(ir.lit("high"), s))
    const right = ir.concat(s, ir.concat(ir.lit("level:high"), s))
    assert.equal(ir.eq(left, right), ir.TRUE)
  })
  test("folds constants with JavaScript's bigint semantics", () => {
    assert.deepEqual(ir.div(ir.lit(-7n), ir.lit(2n)), ir.lit(-3n))
    assert.deepEqual(ir.mod(ir.lit(-7n), ir.lit(2n)), ir.lit(-1n))
    assert.equal(ir.eq(ir.add(a, ir.lit(0n)), a), ir.TRUE)
  })
  test("never folds a division by zero", () => {
    assert.equal(ir.div(ir.lit(1n), ir.lit(0n)).t, "op")
    assert.throws(() => ir.evaluate(ir.div(ir.lit(1n), ir.lit(0n)), new Map()), ir.EvaluationError)
    assert.throws(() => ir.compile(ir.div(ir.lit(1n), ir.lit(0n)))(new Map()), ir.EvaluationError)
  })
  test("compiled evaluator preserves short-circuiting and matches evaluate on shared DAGs", () => {
    const b = ir.variable("b", "int")
    // Division by b appears twice on the right of `&&`; b = 0n must short-circuit to false without throwing.
    const q = ir.div(a, b)
    const guarded = ir.and(ir.not(ir.eq(b, ir.lit(0n))), ir.eq(ir.add(q, q), ir.mul(q, ir.lit(2n))))
    const fn = ir.compile(guarded)
    assert.equal(fn(new Map([["a", 10n], ["b", 0n]])), false)
    assert.equal(fn(new Map([["a", -7n], ["b", 2n]])), true)
    assert.equal(ir.compile(ir.neg(ir.lit(-1n)))(new Map()), 1n)
    assert.equal(ir.compile(ir.sub(a, ir.lit(-1n)))(new Map([["a", 3n]])), 4n)
  })
})

describe("extended subset, shrinking, emit annotations and watch session", () => {
  for (const crossCheck of [true, false]) {
    test(`extended constructs (null, typeof, in, Object.*, arrays, Map.delete, strings, matchers, toThrow, ranges) pass ${crossCheck ? "with" : "without"} cross-check`, async () => {
      const report = await run({ cwd: join(fixtures, "extended"), cache: false, crossCheck })
      assert.deepEqual(report.errors, [])
      assert.deepEqual(report.warnings, [])
      assert.ok(report.laws.length >= 30)
      for (const entry of report.laws) {
        const expected = announced(entry.name)
        assert.equal(entry.status, crossCheck || expected === "proved" ? expected : "failed", `${entry.name}: ${JSON.stringify(entry.findings)} ${entry.notes.join(" ")}`)
        const own = entry.name.split(" > ").at(-1)!
        if (!crossCheck && own.startsWith("FALSE:")) {
          assert.ok(entry.findings.length > 0 && entry.findings.every(f => f.kind === "counterexample" || f.kind === "throws" || f.kind === "inexact"), `${entry.name}: ${JSON.stringify(entry.findings)}`)
        }
      }
      assert.deepEqual(report.laws.flatMap(entry => entry.findings).filter(f => f.kind === "mismatch"), [])
      const ranged = law(report, "matchers and range quantification > large consecutive finite ranges quantify cleanly")
      assert.equal(ranged.status, "proved")
      assert.ok(ranged.cases >= 80_000)
    })
  }

  test("counterexamples on unbounded inputs are shrunk to minimal values, including strings", () => {
    const x0 = ir.variable("x0", "int")
    const x1 = ir.variable("x1", "int")
    const binders: ir.Binder[] = [{ name: "x0", label: "x", ty: "int" }, { name: "x1", label: "y", ty: "int" }]
    const cond = ir.and(ir.lt(ir.lit(500n), x0), ir.and(ir.lt(ir.lit(500n), x1), ir.lt(ir.lit(1005n), ir.add(x0, x1))))
    const { found } = findInput(binders, cond)
    assert.ok(found)
    assert.deepEqual(showInputs(binders, found), { x: "501n", y: "505n" })

    const s0 = ir.variable("s0", "str")
    const sBinders: ir.Binder[] = [{ name: "s0", label: "s", ty: "str" }]
    // Only `"abcdef"` and `"abc"` satisfy this; `"abc"` is not a literal in the formula, so shrinking must discover and keep it.
    const sCond = ir.or(ir.eq(s0, ir.lit("abcdef")), ir.eq(ir.concat(s0, ir.lit("def")), ir.lit("abcdef")))
    const sRes = findInput(sBinders, sCond)
    assert.ok(sRes.found)
    assert.equal(sRes.found.get("s0"), "abc")
  })

  test("deep IR expressions evaluate, compile, substitute, search and build Lean checks without stack overflow", () => {
    const x = ir.variable("x0", "int")
    const y = ir.variable("x1", "int")
    let expr: ir.Expr = x
    for (let i = 0; i < 2000; i++) expr = ir.add(ir.add(expr, y), ir.lit(1n))
    assert.equal(ir.evaluate(expr, new Map([["x0", 5n], ["x1", 0n]])), 2005n)
    assert.equal(ir.compile(expr)(new Map([["x0", 5n], ["x1", 0n]])), 2005n)
    const sub = ir.substitute(expr, new Map([["x0", ir.lit(10n)], ["x1", ir.lit(0n)]]))
    assert.equal(ir.evaluate(sub, new Map()), 2010n)
    const { found } = findInput([{ name: "x0", label: "x", ty: "int" }, { name: "x1", label: "y", ty: "int" }], ir.lt(ir.lit(2000n), expr))
    assert.ok(found)
    const finiteBinders: ir.Binder[] = [
      { name: "x0", label: "x", ty: "int", domain: Array.from({ length: 20 }, (_, i) => BigInt(i)) },
      { name: "x1", label: "y", ty: "int", domain: Array.from({ length: 20 }, (_, i) => BigInt(i)) },
    ]
    const checks = checksFor(finiteBinders, ir.TRUE, ir.le(ir.lit(0n), expr), undefined)
    assert.equal(checks.length, 1)
    assert.equal(checks[0]?.cases, 400)
    // Also exercise `longestString` on a deep finite-only expression.
    const smallBinders: ir.Binder[] = [
      { name: "x0", label: "x", ty: "int", domain: [0n, 1n] },
      { name: "x1", label: "y", ty: "int", domain: [0n, 1n] },
    ]
    const finiteChecks = checksFor(smallBinders, ir.TRUE, ir.le(ir.lit(0n), expr), undefined)
    assert.equal(finiteChecks.length, 1)
  })

  test("finite case count is attributed even when an earlier specialization simplifies away", () => {
    const x = ir.variable("x0", "int")
    const y = ir.variable("x1", "int")
    const binders: ir.Binder[] = [
      { name: "x0", label: "x", ty: "int", domain: [0n, 1n] },
      { name: "x1", label: "y", ty: "int", domain: Array.from({ length: 200 }, (_, i) => BigInt(i)) },
    ]
    // x = 0 simplifies to TRUE; x = 1 stays a quantified check and must carry all 400 finite cases.
    const claim = ir.or(ir.eq(x, ir.lit(0n)), ir.le(ir.lit(0n), y))
    const checks = checksFor(binders, ir.TRUE, claim, undefined)
    assert.equal(checks.reduce((n, c) => n + c.cases, 0), 400)
  })

  test("--emit includes law annotations (escaping multiline names) and unproved diagnostics include binder names", async () => {
    const emitFile = join(cacheDirectory, "annotated.lean")
    const report = await run({ cwd: join(fixtures, "suite"), cache: false, emit: emitFile })
    const leanText = readFileSync(emitFile, "utf8")
    assert.match(leanText, /^-- .+ ".*" \(/m)
    const unproved = law(report, "UNPROVED: a product of positives is positive")
    assert.match(unproved.findings[0]?.detail ?? "", /^where x0 = a, x1 = b\n/)

    const multiline = mkdtempSync(join(fixtures, ".tmp-"))
    try {
      const multiEmit = join(multiline, "out.lean")
      writeFileSync(join(multiline, "m.law.ts"), `import { expect, law } from "@bytewaveco/pudding"\nlaw("line one\\nline two", () => expect(1).toBe(1))\n`)
      const multiReport = await run({ cwd: multiline, cache: false, emit: multiEmit })
      assert.equal(multiReport.ok, true)
      const emitted = readFileSync(multiEmit, "utf8")
      assert.match(emitted, /-- .* "line one\\nline two"/)
      assert.doesNotMatch(emitted, /^line two/m)
    } finally {
      rmSync(multiline, { recursive: true, force: true })
    }
  })

  test("WatchSession detects edits to both value and type-only files without stale results", async () => {
    const project = mkdtempSync(join(fixtures, ".tmp-"))
    const session = createWatchSession()
    try {
      writeFileSync(join(project, "types.ts"), `export type Role = "admin"\n`)
      writeFileSync(join(project, "auth.ts"), `import type { Role } from "./types.ts"\nexport const canWrite = (role: Role) => role === "admin"\n`)
      writeFileSync(join(project, "auth.law.ts"), `import { domain, expect, law } from "@bytewaveco/pudding"
import type { Role } from "./types.ts"
import { canWrite } from "./auth.ts"
law("every role can write", domain<Role>(), role => expect(canWrite(role)).toBe(true))
`)
      const first = await run({ cwd: project, cache: false, session })
      assert.equal(first.ok, true)

      // Edit a type-only dependency: session.affected must include auth.law.ts and re-checking must see the new union member.
      writeFileSync(join(project, "types.ts"), `export type Role = "admin" | "guest"\n`)
      const affectedType = session.affected(join(project, "types.ts"))
      assert.ok(affectedType && affectedType.some(file => file.endsWith("auth.law.ts")))
      const afterTypeEdit = await run({ cwd: project, cache: false, session, lawFiles: affectedType })
      assert.equal(afterTypeEdit.ok, false)
      assert.deepEqual(law(afterTypeEdit, "every role can write").findings[0]?.inputs, { role: '"guest"' })

      // Edit the value module so the law passes again: session with changedFiles reuses the open compiler API and sees the edit immediately.
      writeFileSync(join(project, "auth.ts"), `import type { Role } from "./types.ts"\nexport const canWrite = (_role: Role) => true\n`)
      const affectedValue = session.affected(join(project, "auth.ts"))
      assert.ok(affectedValue && affectedValue.some(file => file.endsWith("auth.law.ts")))
      const afterValueEdit = await run({ cwd: project, cache: false, session, lawFiles: affectedValue, changedFiles: [join(project, "auth.ts")] })
      assert.equal(afterValueEdit.ok, true)

      // Triple-slash `/// <reference path="..." />` directives (including indentation/spaces) must also be tracked, and deleted law files pruned on full runs.
      writeFileSync(join(project, "ambient.d.ts"), `declare type Flag = "on"\n`)
      writeFileSync(join(project, "flag.law.ts"), `  /// <reference path = "./ambient.d.ts" />\nimport { domain, expect, law } from "@bytewaveco/pudding"\nlaw("flag is on", domain<Flag>(), f => expect(f).toBe("on"))\n`)
      assert.equal((await run({ cwd: project, cache: false, session })).ok, true)
      writeFileSync(join(project, "ambient.d.ts"), `declare type Flag = "on" | "off"\n`)
      const affectedRef = session.affected(join(project, "ambient.d.ts"))
      assert.ok(affectedRef && affectedRef.some(file => file.endsWith("flag.law.ts")))
      assert.equal((await run({ cwd: project, cache: false, session, lawFiles: affectedRef })).ok, false)

      rmSync(join(project, "flag.law.ts"))
      assert.equal((await run({ cwd: project, cache: false, session })).ok, true)
      assert.deepEqual(session.affected(join(project, "ambient.d.ts")), [])

      // Deleting the final law clears the dependency graph on a full run too.
      rmSync(join(project, "auth.law.ts"))
      assert.equal((await run({ cwd: project, cache: false, session })).ok, false)
      assert.equal(session.affected(join(project, "auth.ts")), undefined)
    } finally {
      session.close()
      rmSync(project, { recursive: true, force: true })
    }
  })

  test("cross-check preserves __proto__ as an own property on input records", async () => {
    const project = mkdtempSync(join(fixtures, ".tmp-"))
    try {
      writeFileSync(join(project, "proto.law.ts"), `import { domain, expect, law } from "@bytewaveco/pudding"
law("own __proto__ property survives cross-check", domain<{ ["__proto__"]: 1; a: 2 }>(), x => {
  expect(x.a).toBe(2)
})
`)
      const report = await run({ cwd: project, cache: false })
      assert.equal(report.ok, true, JSON.stringify(report.laws))
      assert.equal(law(report, "own __proto__ property survives cross-check").status, "proved")
    } finally {
      rmSync(project, { recursive: true, force: true })
    }
  })

  test("assertStable refuses module array tables mutated via callback-taking array methods", async () => {
    const project = mkdtempSync(join(fixtures, ".tmp-"))
    try {
      writeFileSync(join(project, "evil.ts"), `export const A = [1, 2, 3]
const _m = A.map((_, __, arr) => { arr[0] = 999; return 0 })
export const B = [1, 2, 3]
const _r = B.reduce((s, _, __, arr) => { arr[0] = 999; return s }, 0)
export const C = [1, 2, 3]
const _f = C.map(function (x) { (arguments[2] as number[])[0] = 999; return x })
export const SAFE = [1, 2, 3]
const _ok = SAFE.map(x => x + 1)
export const readA = () => A[0]
export const readB = () => B[0]
export const readC = () => C[0]
export const readSafe = () => SAFE[0]
`)
      writeFileSync(join(project, "evil.law.ts"), `import { expect, law } from "@bytewaveco/pudding"
import { readA, readB, readC, readSafe } from "./evil.ts"
law("FALSE: A[0] is 1", () => expect(readA()).toBe(1))
law("FALSE: B[0] is 1", () => expect(readB()).toBe(1))
law("FALSE: C[0] is 1", () => expect(readC()).toBe(1))
law("SAFE[0] is 1", () => expect(readSafe()).toBe(1))
`)
      for (const crossCheck of [false, true]) {
        const report = await run({ cwd: project, cache: false, crossCheck })
        for (const name of ["FALSE: A[0] is 1", "FALSE: B[0] is 1", "FALSE: C[0] is 1"]) {
          assert.equal(law(report, name).status, "failed", `${name} (crossCheck=${crossCheck})`)
        }
        assert.equal(law(report, "SAFE[0] is 1").status, "proved")
      }
    } finally {
      rmSync(project, { recursive: true, force: true })
    }
  })

  test("IR same/concat handle deep shared DAGs, algebraic rules simplify, and value-based CSE shares separate equal subtrees", () => {
    const x = ir.variable("x0", "int")
    let a: ir.Expr = x
    let b: ir.Expr = x
    for (let i = 0; i < 60; i++) {
      a = ir.add(a, a)
      b = ir.add(b, b)
    }
    assert.equal(ir.same(a, b), true)
    assert.equal(ir.same(a, ir.add(b, ir.lit(1n))), false)

    let chain: ir.Expr = ir.variable("s0", "str")
    for (let i = 0; i < 2000; i++) chain = ir.concat(chain, ir.lit("a"))
    assert.equal(chain.t === "op" && chain.args[1]?.t === "lit" && (chain.args[1].value as string).length === 2000, true)

    assert.equal(ir.same(ir.not(ir.lt(x, ir.lit(0n))), ir.le(ir.lit(0n), x)), true)
    assert.equal(ir.and(ir.lt(x, ir.lit(0n)), ir.le(ir.lit(0n), x)), ir.FALSE)
    assert.equal(ir.same(ir.add(ir.add(x, ir.lit(2n)), ir.lit(3n)), ir.add(x, ir.lit(5n))), true)
    assert.equal(ir.same(ir.sub(ir.add(x, ir.lit(3n)), ir.lit(3n)), x), true)

    const makeBig = () => ir.add(ir.mul(x, ir.lit(3n)), ir.sub(ir.mul(x, ir.lit(7n)), ir.lit(11n)))
    const [check] = checksFor([{ name: "x0", label: "x", ty: "int" }], ir.TRUE, ir.lt(makeBig(), ir.add(makeBig(), ir.lit(1n))), undefined)
    assert.ok(check)
    assert.match(check.statement, /let _v0 :=/)
  })

  test("enums (string, numeric, const enum) prove and cross-check cleanly, and ordering/vacuity/type-elision/4-var search work", async () => {
    const vars = [0, 1, 2, 3].map(i => ir.variable(`x${i}`, "int"))
    const binders: ir.Binder[] = vars.map((v, i) => ({ name: v.t === "var" ? v.name : "", label: `v${i}`, ty: "int" }))
    const allZero = ir.all(vars.map(v => ir.eq(v, ir.lit(0n))))
    const found = findInput(binders, allZero)
    assert.deepEqual(found.found ? showInputs(binders, found.found) : undefined, { v0: "0n", v1: "0n", v2: "0n", v3: "0n" })

    const project = mkdtempSync(join(fixtures, ".tmp-"))
    try {
      writeFileSync(join(project, "types.ts"), `export default interface DefaultT { v: bigint }
export type A = bigint
export type B = bigint
export enum Role { Viewer = "viewer", Admin = "admin" }
export enum Priority { Low }
export enum Priority { High = 10 }
export const enum Flags { Read = 1, Write = 2 }
`)
      writeFileSync(join(project, "order.law.ts"), `import { domain, expect, law } from "@bytewaveco/pudding"
import DefaultT /* comment before comma */, { type A, B, Role, Priority, Flags } from "./types"
law("enums work as domains and values", domain<{ role: Role; prio: Priority; flag: Flags }>(), ({ role, prio, flag }) => {
  expect(role === Role.Viewer || role === Role.Admin).toBe(true)
  expect(Priority[prio]).toBe(prio === Priority.Low ? "Low" : "High")
  expect(flag === Flags.Read || flag === Flags.Write).toBe(true)
})
law("FALSE: x is greater than 5", domain<A>(), (x: B) => {
  const _box: DefaultT = { v: x }
  expect(_box.v).toBeGreaterThan(5n)
})
law("VACUOUS: impossible arithmetic", domain<bigint>(), x => {
  if (x > 10n && x < 5n) expect(x).toBeGreaterThan(0n)
})
law("optional tuple refused", domain<[bigint, bigint?]>(), items => {
  expect(items.length === 1 || items.length === 2).toBe(true)
})
`)
      const first = await run({ cwd: project })
      assert.deepEqual(first.errors, [])
      assert.deepEqual(first.warnings, [])
      assert.equal(law(first, "enums work as domains and values").status, "proved")
      assert.equal(law(first, "optional tuple refused").status, "failed")
      assert.equal(law(first, "optional tuple refused").findings[0]?.kind, "unsupported")
      const gt = law(first, "FALSE: x is greater than 5")
      assert.equal(gt.status, "failed")
      assert.match(gt.findings[0]?.detail ?? "", /actual: +.*\nexpected: > 5n/)
      assert.deepEqual(law(first, "VACUOUS: impossible arithmetic").findings.map(f => f.kind), ["vacuous"])
      const second = await run({ cwd: project })
      assert.deepEqual(law(second, "VACUOUS: impossible arithmetic").findings.map(f => f.kind), ["vacuous"])
    } finally {
      rmSync(project, { recursive: true, force: true })
    }
  })
})
