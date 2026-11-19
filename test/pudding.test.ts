import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { cpSync, existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { after, before, describe, test } from "node:test"
import * as ir from "../src/ir.ts"
import { checksFor, FAST_HEADER, prove } from "../dist/lean.js"
import { locateLean, run, type Report } from "../dist/runner.js"

const fixtures = join(import.meta.dirname, "fixtures")
const lean = locateLean({}, join(import.meta.dirname, ".."))
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
    assert.match(sampled.notes[0] ?? "", /not proved: the array method `\.filter` is not supported \(fallback\.ts:2:10\)/)
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
    assert.match(note("SAMPLED: a closure that writes an outer variable"), /uses `count`, a variable that is reassigned outside it/)
    assert.match(note("CHECKED: a closure that reads a reassigned variable"), /uses `value`, a variable that is reassigned outside it/)
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
      assert.equal(report.laws.length, 39)
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

test("a value that grows with every round of a loop is refused quickly, not handed to Lean", async () => {
  // This once produced a 33 MB theorem that Lean spent minutes on.
  const report = await run({ cwd: join(fixtures, "growth"), cache: false })
  const entry = law(report, "settling never grows the value")
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
  assert.match(note("REFUSED: a push on one side of a condition that is not known"), /grows on only one side of a condition/)
  assert.match(note("REFUSED: a change on the right of &&"), /the right side of `&&` changes an object in place/)
  assert.match(note("REFUSED: a change inside a callback of some"), /a callback of `\.some` changes an object in place/)
  assert.match(note("REFUSED: an object stored inside itself"), /inside itself/)
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
    assert.match(law(report, "REJECTED: a script that hides a parenthesis in a comment").findings[0]?.message ?? "", /may not contain comments/)
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
  })
})
