import assert from "node:assert/strict"
import { cpSync, existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
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

  test("what cannot be modeled exactly is refused by name", () => {
    const note = (name: string) => law(report, name).notes[0] ?? ""
    assert.match(note("SAMPLED: a closure that writes an outer variable"), /uses `count`, a variable that is reassigned outside it/)
    assert.match(note("CHECKED: a closure that reads a reassigned variable"), /uses `value`, a variable that is reassigned outside it/)
    assert.match(note("SAMPLED: mutating an object in place"), /changing an object or array in place is not modeled/)
    assert.match(note("SAMPLED: mutating an array in place"), /changing an object or array in place is not modeled/)
    assert.match(note("SAMPLED: assignment used as a value"), /assignment used as a value/)
    assert.match(note("CHECKED: a while loop bounded by an input"), /how many times this loop runs depends on a value that is not known here/)
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

  test("the project needs no tsconfig of its own", () => {
    assert.equal(existsSync(join(cwd, "tsconfig.json")), false)
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
  assert.match(entry.notes[0] ?? "", /runs a statement at line 8 when it loads/)
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

  test("an unchanged project reuses its result, and an edit reproves only what changed", async () => {
    const first = await run({ cwd: directory })
    assert.equal(first.replayed, false)
    assert.equal(first.cachedObligations, 0)

    const second = await run({ cwd: directory })
    assert.equal(second.replayed, true)
    assert.deepEqual(second.laws, first.laws)

    const file = join(directory, "shapes.law.ts")
    writeFileSync(file, readFileSync(file, "utf8") + `
law("a rectangle of height two has twice its width as area", domain<bigint>(), width => {
  expect(area({ kind: "rect", width, height: 2n })).toEqual(width + width)
})
`)
    const third = await run({ cwd: directory })
    assert.equal(third.replayed, false)
    assert.equal(third.laws.length, first.laws.length + 1)
    assert.equal(law(third, "a rectangle of height two has twice its width as area").status, "proved")
    // Proved theorems are remembered; the two rejected ones of the false law are tried again.
    assert.equal(third.obligations - third.cachedObligations, 3)
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

  test("rejects a wrong claim about division, so the agreement test can fail", async () => {
    const wrong = checksFor([x], ir.TRUE, ir.eq(ir.div(vx, ir.lit(2n)), ir.lit(-4n)), undefined).map(c => c.statement)
    const [outcome] = await prove(lean, FAST_HEADER, wrong)
    assert.equal(outcome?.ok, false)
  })
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
