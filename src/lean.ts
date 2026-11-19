// Print obligations as Lean theorems and run Lean over them.

import { execFile } from "node:child_process"
import { mkdtemp, rm, writeFile } from "node:fs/promises"
import { availableParallelism, tmpdir } from "node:os"
import { join } from "node:path"
import * as ir from "./ir.ts"
import type { Binder, Expr, Scalar } from "./ir.ts"

/**
 * The modules the generated theorems need. Importing only these starts Lean
 * several times faster than `import Init`, and they are what a trimmed Lean
 * runtime ships.
 */
export const FAST_IMPORTS = [
  "Init.Core", "Init.Omega", "Init.Grind", "Init.Data.List.Basic", "Init.Data.String.Basic", "Init.Data.Int.DivMod", "Init.Data.Int.OfNat",
]

/**
 * A slightly larger set for a second attempt. Measured against the whole of
 * `Init` on thousands of generated theorems, the fallback tactic proves
 * exactly as much under these imports.
 */
export const FALLBACK_IMPORTS = [...FAST_IMPORTS, "Init.Data.String.Lemmas.Basic", "Init.Data.String.Length"]

const header = (imports: readonly string[]) => ["prelude", ...imports.map(name => `import ${name}`)].join("\n")
export const FAST_HEADER = header(FAST_IMPORTS)
export const FALLBACK_HEADER = header(FALLBACK_IMPORTS)
/** The whole core library, for proofs an author wrote. A trimmed runtime does not have it. */
export const FULL_HEADER = "import Init"

export const DEFAULT_TACTIC = "grind"
const FINITE_TACTIC = "decide +kernel"
/** Tried, under the fallback imports, on statements the default tactic could not close. */
const FALLBACK_TACTIC = "first | grind | (intros; simp_all; done) | (intros; simp_all <;> omega)"
const MAX_TERM_SIZE = 200_000
/**
 * The most text one expression may come to. A value fed back into itself in a
 * loop multiplies in size with every round, and Lean's time grows with it:
 * about five seconds at this size, and minutes a few rounds later.
 */
const MAX_TERM_TEXT = 120_000
/** How long one Lean process may run: this much, plus a share for each theorem in its file. */
const FILE_TIMEOUT_MS = 30_000
const THEOREM_TIMEOUT_MS = 10_000
const MAX_SPECIALIZATIONS = 512

/**
 * Why an author's proof script cannot be used, if it cannot. The script is
 * placed inside parentheses in the theorem, and that only confines it if every
 * parenthesis in its text is one Lean sees. So the things that can hide a
 * parenthesis from Lean (comments, string and character literals, quoted
 * names) are not allowed, and the parentheses must balance.
 */
export function scriptProblem(script: string): string | undefined {
  if (/--|\/-|"|«/.test(script)) return "a proof script may not contain comments, string literals or «quoted names»"
  if (/'[()\[\]{}⟨⟩\\]/.test(script)) return "a proof script may not contain character literals"
  let depth = 0
  for (const char of script) {
    if (char === "(") depth++
    else if (char === ")" && --depth < 0) break
  }
  return depth === 0 ? undefined : "the parentheses in the proof script do not balance"
}

/** How a statement is proved: by evaluating every case, by the default automation, or by the author's script. */
export function proofKind(statement: string): "finite" | "automatic" | "authored" {
  if (statement.endsWith(` := by ${FINITE_TACTIC}`)) return "finite"
  return statement.endsWith(` := by ${DEFAULT_TACTIC}`) || statement.endsWith(` := by ${FALLBACK_TACTIC}`) ? "automatic" : "authored"
}

/** The same statement with the stronger, slower automation. Only meaningful for an automatic statement. */
export function withFallback(statement: string): string {
  return statement.slice(0, -DEFAULT_TACTIC.length) + FALLBACK_TACTIC
}

export class TooLarge extends Error {}

function leanString(text: string): string {
  let out = '"'
  for (const char of text) {
    const code = char.codePointAt(0)!
    if (char === '"' || char === "\\") out += "\\" + char
    else if (code >= 0x20 && code < 0x7f) out += char
    else if (code < 0x10000) out += "\\u" + code.toString(16).padStart(4, "0")
    else out += char
  }
  return out + '"'
}

function leanScalar(value: Scalar): string {
  if (typeof value === "boolean") return String(value)
  if (typeof value === "bigint") return `(${value} : Int)`
  return leanString(value)
}

function print(e: Expr, memo: Map<Expr, string>): string {
  if (e.t === "var") return e.name
  if (e.t === "lit") return leanScalar(e.value)
  const known = memo.get(e)
  if (known !== undefined) return known
  const [a, b, c] = e.args.map(arg => print(arg, memo)) as [string, string, string]
  let text: string
  switch (e.op) {
    case "not": text = `(!${a})`; break
    case "and": text = `(${a} && ${b})`; break
    case "or": text = `(${a} || ${b})`; break
    case "eq": text = `(${a} == ${b})`; break
    case "lt": text = `(decide (${a} < ${b}))`; break
    case "le": text = `(decide (${a} ≤ ${b}))`; break
    case "add": text = `(${a} + ${b})`; break
    case "sub": text = `(${a} - ${b})`; break
    case "mul": text = `(${a} * ${b})`; break
    case "neg": text = `(-${a})`; break
    case "concat": text = `(${a} ++ ${b})`; break
    case "str": text = `(toString ${a})`; break
    case "ite": text = `(if ${a} then ${b} else ${c})`; break
    case "fdiv": {
      // Lean's `/` on integers rounds toward minus infinity when the divisor
      // is positive, so a literal divisor needs no case split.
      const divisor = e.args[1]!
      if (divisor.t === "lit" && (divisor.value as bigint) > 0n) text = `(${a} / ${divisor.value})`
      else if (divisor.t === "lit" && (divisor.value as bigint) < 0n) text = `((-${a}) / ${-(divisor.value as bigint)})`
      else text = `(Int.fdiv ${a} ${b})`
      break
    }
    case "div":
    case "mod": {
      // BigInt division truncates toward zero and the remainder takes the sign
      // of the dividend. With a literal divisor both are written with Lean's
      // `/` and `%` on non-negative operands, which the arithmetic tactics
      // understand. A zero divisor is excluded by a separate obligation.
      const divisor = e.args[1]!
      const symbol = e.op === "div" ? "/" : "%"
      if (divisor.t === "lit" && divisor.value !== 0n) {
        const magnitude = (divisor.value as bigint) < 0n ? -(divisor.value as bigint) : (divisor.value as bigint)
        const flip = e.op === "div" && (divisor.value as bigint) < 0n
        const body = `(if (0 : Int) ≤ ${a} then ${a} ${symbol} ${magnitude} else -((-${a}) ${symbol} ${magnitude}))`
        text = flip ? `(-${body})` : body
      } else text = `(Int.${e.op === "div" ? "tdiv" : "tmod"} ${a} ${b})`
      break
    }
  }
  memo.set(e, text)
  return text
}

function printExpr(e: Expr): string {
  if (ir.treeSize(e) > MAX_TERM_SIZE) throw new TooLarge("the translated expression is too large to check")
  const text = print(e, new Map())
  if (text.length > MAX_TERM_TEXT) throw new TooLarge("the translated expression is too large to check")
  return text
}

function leanType(ty: ir.Ty): string {
  return { bool: "Bool", int: "Int", str: "String" }[ty]
}

/** The proposition `guard → claim` as a single boolean. */
function implication(guard: Expr, claim: Expr): Expr {
  return ir.or(ir.not(guard), claim)
}

export interface Check {
  /** Everything after the theorem name. Also the cache key, together with the Lean version. */
  statement: string
  /** Number of concrete cases the theorem covers when it is decided by evaluation. */
  cases: number
}

/**
 * Theorems that together state `∀ binders, guard → claim`.
 *
 * When every input is finite there is one theorem, decided by evaluating all
 * cases in Lean's kernel. Otherwise the finite inputs are specialized away and
 * each remaining theorem quantifies over the unbounded ones.
 */
/** The bounds of a finite integer input whose values are consecutive, when it has more than a couple. */
function consecutive(binder: Binder): [bigint, bigint] | undefined {
  const values = binder.domain
  if (binder.ty !== "int" || !values || values.length < 3) return undefined
  const sorted = (values as bigint[]).toSorted((a, b) => (a < b ? -1 : a > b ? 1 : 0))
  return sorted.every((value, i) => i === 0 || value === sorted[i - 1]! + 1n) ? [sorted[0]!, sorted.at(-1)!] : undefined
}

/** Whether a variable is divided by, or multiplied with something that is not a constant. */
function usedNonlinearly(e: Expr, name: string, seen = new Set<Expr>()): boolean {
  if (e.t !== "op" || seen.has(e)) return false
  seen.add(e)
  const mentions = (part: Expr) => ir.freeVariables(part).has(name)
  const [a, b] = e.args as [Expr, Expr]
  if ((e.op === "div" || e.op === "mod" || e.op === "fdiv") && mentions(b)) return true
  if (e.op === "mul" && a.t !== "lit" && b.t !== "lit" && (mentions(a) || mentions(b))) return true
  return e.args.some(arg => usedNonlinearly(arg, name, seen))
}

export function checksFor(binders: readonly Binder[], guard: Expr, claim: Expr, tactic: string | undefined): Check[] {
  const body = implication(guard, claim)
  const free = ir.freeVariables(body)
  const used = binders.filter(b => free.has(b.name))
  if (used.every(b => b.domain)) {
    const cases = used.reduce((n, b) => n * b.domain!.length, 1)
    let text = printExpr(body)
    for (const binder of [...used].reverse()) {
      text = `([${binder.domain!.map(leanScalar).join(", ")}].all fun ${binder.name} => ${text})`
    }
    return [{ statement: ` : ${text} = true := by ${FINITE_TACTIC}`, cases }]
  }
  // An integer input over a run of consecutive values does not have to be
  // split into cases: its bounds can be stated instead, which the arithmetic
  // tactics use directly. Splitting is kept where the input is multiplied or
  // divided by, because fixing its value is what makes that arithmetic linear.
  const bounded = new Map<string, [bigint, bigint]>()
  for (const binder of used) {
    const range = consecutive(binder)
    if (range && !usedNonlinearly(body, binder.name)) bounded.set(binder.name, range)
  }
  const finite = used.filter(b => b.domain && !bounded.has(b.name))
  const symbolic = used.filter(b => !b.domain || bounded.has(b.name))
  for (const [name, [low, high]] of bounded) {
    const input = ir.variable(name, "int")
    guard = ir.and(ir.and(ir.le(ir.lit(low), input), ir.le(input, ir.lit(high))), guard)
  }
  const combinations = finite.reduce((n, b) => n * b.domain!.length, 1)
  if (combinations > MAX_SPECIALIZATIONS) {
    throw new TooLarge(`the finite inputs have ${combinations} combinations alongside unbounded ones; the limit is ${MAX_SPECIALIZATIONS}`)
  }
  // An author's script goes inside parentheses, so that it has to be a complete
  // tactic sequence and nothing after it can be read as part of it.
  const script = tactic === undefined ? DEFAULT_TACTIC : `(\n  ${tactic.trim().split("\n").join("\n  ")}\n)`
  const checks: Check[] = []
  const visit = (index: number, values: Map<string, Expr>) => {
    if (index < finite.length) {
      for (const value of finite[index]!.domain!) visit(index + 1, new Map(values).set(finite[index]!.name, ir.lit(value)))
      return
    }
    const g = ir.substitute(guard, values)
    const c = ir.substitute(claim, values)
    if (implication(g, c) === ir.TRUE) return
    const remaining = ir.freeVariables(implication(g, c))
    const parameters = symbolic.filter(b => remaining.has(b.name)).map(b => ` (${b.name} : ${leanType(b.ty)})`).join("")
    const proposition = g === ir.TRUE ? `${printExpr(c)} = true` : `${printExpr(g)} = true → ${printExpr(c)} = true`
    checks.push({ statement: `${parameters} : ${proposition} := by ${script}`, cases: 0 })
  }
  visit(0, new Map())
  return checks
}

export interface LeanOutcome {
  ok: boolean
  /** Lean's message when the theorem was rejected. */
  message: string
}

interface LeanMessage {
  severity: string
  pos?: { line: number }
  data: string
}

/** Lean was stopped because it ran past its time limit. */
class LeanTimeout extends Error {}

function runFile(lean: string, source: string, directory: string, name: string, timeout: number): Promise<LeanMessage[]> {
  return new Promise((resolve, reject) => {
    const file = join(directory, name)
    writeFile(file, source).then(() => {
      // Lean stops reporting after 100 errors unless told otherwise, and a theorem it never reported on must not pass for proved.
      execFile(lean, ["-DmaxErrors=0", "--json", file], { maxBuffer: 1 << 28, timeout, killSignal: "SIGKILL" }, (error, stdout, stderr) => {
        if (error?.killed) return reject(new LeanTimeout())
        if (error && typeof (error as NodeJS.ErrnoException).code === "string") {
          return reject(new Error(`could not run Lean at ${lean}: ${error.message}`))
        }
        const messages: LeanMessage[] = []
        for (const line of stdout.split("\n")) {
          if (!line.startsWith("{")) continue
          try {
            messages.push(JSON.parse(line) as LeanMessage)
          } catch {
            // Not a diagnostic line.
          }
        }
        if (error && !messages.some(m => m.severity === "error")) {
          return reject(new Error(`Lean exited abnormally: ${(stderr || stdout).trim().slice(0, 2000)}`))
        }
        resolve(messages)
      })
    }, reject)
  })
}

/** The axioms of Lean's own logic. A proof that rests on anything else, `sorry` above all, is not a proof. */
const ACCEPTED_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"])

async function runChunk(lean: string, header: string, statements: string[], directory: string, name: string, strict: boolean, timeout: number): Promise<LeanOutcome[]> {
  // Each theorem is followed by a question about it: which axioms does it
  // rest on? A theorem counts as proved only when Lean reports no error for
  // it *and* answers that question acceptably. Silence is never taken for
  // success, and neither is an unfinished proof, which Lean only warns about.
  const lines = header.split("\n")
  const firstLine: number[] = []
  const askedAt: number[] = []
  for (const [i, statement] of statements.entries()) {
    firstLine.push(lines.length + 1)
    lines.push(...`theorem c${i}${statement}`.split("\n"))
    askedAt.push(lines.length + 1)
    lines.push(`#print axioms c${i}`)
  }
  // The file ends with a command that always answers, to show that Lean reached the end.
  const sentinel = lines.length + 1
  lines.push("#check Nat")
  const messages = await runFile(lean, lines.join("\n") + "\n", directory, name, timeout)
  if (!messages.some(message => message.severity === "information" && message.pos?.line === sentinel)) {
    throw new Error("Lean stopped before it had checked every theorem, so no result can be trusted")
  }
  const outcomes: LeanOutcome[] = statements.map(() => ({ ok: false, message: "" }))
  const failed = new Set<number>()
  const reject = (index: number, text: string) => {
    const outcome = outcomes[index]!
    outcome.message = outcome.message ? outcome.message + "\n" + text : text
    failed.add(index)
  }
  for (const message of messages) {
    const line = message.pos?.line ?? 0
    let index = -1
    for (let i = 0; i < firstLine.length && firstLine[i]! <= line; i++) index = i
    if (message.severity === "error") {
      // An error after the last theorem means something in the file disturbed what follows it. Trust none of it.
      if (line >= sentinel) return statements.map(() => ({ ok: false, message: `Lean reported an error after the theorems: ${message.data}` }))
      if (index < 0) throw new Error(`Lean rejected the generated preamble: ${message.data}`)
      // An error on the question itself only repeats that the theorem above it failed.
      if (line !== askedAt[index] || !failed.has(index)) reject(index, message.data)
    } else if (index >= 0 && line === askedAt[index] && message.severity === "information") {
      const listed = /depends on axioms: \[([^\]]*)\]/.exec(message.data)
      const foreign = listed ? listed[1]!.split(",").map(axiom => axiom.trim()).filter(axiom => axiom && !ACCEPTED_AXIOMS.has(axiom)) : []
      if (foreign.includes("sorryAx")) {
        if (!failed.has(index)) reject(index, "the proof is unfinished: it uses `sorry`")
      } else if (foreign.length) reject(index, `the proof rests on ${foreign.map(axiom => `\`${axiom}\``).join(", ")}, which Pudding does not accept`)
      else if (listed || /does not depend on any axioms/.test(message.data)) outcomes[index]!.ok = true
    }
  }
  for (const index of failed) outcomes[index]!.ok = false
  // A file holding an author's script must be clean throughout: an error anywhere means Lean read something as more than a proof.
  if (strict && messages.some(message => message.severity === "error")) for (const outcome of outcomes) outcome.ok = false
  for (const outcome of outcomes) if (!outcome.ok && !outcome.message) outcome.message = "Lean did not confirm this theorem"
  return outcomes
}

/**
 * Check each statement, in parallel across processes when there are many.
 *
 * Statements Pudding generated share files. A statement that carries an
 * author's proof script gets a file of its own (`alone`), with any error in
 * that file counting against it: Lean recovers from a syntax error by reading
 * on from the next command, so text in a script could otherwise define things
 * that change what the theorems after it mean.
 */
export async function prove(lean: string, header: string, statements: string[], processes = availableParallelism(), alone = false): Promise<LeanOutcome[]> {
  if (!statements.length) return []
  const directory = await mkdtemp(join(tmpdir(), "pudding-"))
  try {
    const chunks: string[][] = []
    if (alone) for (const statement of statements) chunks.push([statement])
    else {
      // Starting Lean costs little next to proving, so spread the work widely.
      const workers = Math.max(1, Math.min(processes, Math.ceil(statements.length / 8)))
      const size = Math.ceil(statements.length / workers)
      for (let i = 0; i < statements.length; i += size) chunks.push(statements.slice(i, i + size))
    }
    // Lean bounds its tactics by work done, not by the clock, and reading a
    // huge theorem is not bounded at all. A file that runs past its time is
    // tried again one theorem at a time, so that only the slow one goes unproved.
    const attempt = async (chunk: string[], file: string): Promise<LeanOutcome[]> => {
      const timeout = FILE_TIMEOUT_MS + THEOREM_TIMEOUT_MS * chunk.length
      try {
        return await runChunk(lean, header, chunk, directory, file, alone, timeout)
      } catch (error) {
        if (!(error instanceof LeanTimeout)) throw error
        if (chunk.length === 1) return [{ ok: false, message: `Lean did not finish within ${timeout / 1000} seconds` }]
        const outcomes: LeanOutcome[] = []
        for (const [n, statement] of chunk.entries()) outcomes.push(...await attempt([statement], `${file.replace(/\.lean$/, "")}_${n}.lean`))
        return outcomes
      }
    }
    const results: LeanOutcome[][] = []
    // At most one process per core at a time.
    for (let i = 0; i < chunks.length; i += Math.max(1, processes)) {
      const wave = chunks.slice(i, i + Math.max(1, processes))
      results.push(...await Promise.all(wave.map((chunk, n) => attempt(chunk, `Proof${i + n}.lean`))))
    }
    return results.flat()
  } finally {
    await rm(directory, { recursive: true, force: true })
  }
}

/** The Lean source for a set of statements, for inspection. */
export function render(header: string, statements: string[]): string {
  return header + "\n\n" + statements.map((statement, i) => `theorem c${i}${statement}`).join("\n\n") + "\n"
}
