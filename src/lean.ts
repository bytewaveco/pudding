// Print obligations as Lean theorems and run Lean over them.

import { execFile } from "node:child_process"
import { mkdtemp, rm, writeFile } from "node:fs/promises"
import { availableParallelism, tmpdir } from "node:os"
import { join } from "node:path"
import * as ir from "./ir.ts"
import type { Binder, Expr, Scalar } from "./ir.ts"

/**
 * The modules the generated theorems need. Importing only these starts Lean
 * several times faster than the default `import Init`. A proof that fails
 * under this header is retried under the full library before it is reported.
 */
export const FAST_HEADER = [
  "prelude",
  "import Init.Core",
  "import Init.Omega",
  "import Init.Grind",
  "import Init.Data.List.Basic",
  "import Init.Data.String.Basic",
  "import Init.Data.Int.DivMod",
].join("\n")

export const FULL_HEADER = "import Init"

export const DEFAULT_TACTIC = "grind"
/** Tried, under the full library, on statements the default tactic could not close. */
const FALLBACK_TACTIC = "first | grind | (intros; simp_all; done) | (intros; simp_all <;> omega)"

/** The same statement with the stronger, slower automation, or undefined when the author supplied the proof. */
export function withFallback(statement: string): string | undefined {
  const ending = ` := by ${DEFAULT_TACTIC}`
  return statement.endsWith(ending) ? statement.slice(0, -DEFAULT_TACTIC.length) + FALLBACK_TACTIC : undefined
}
const FINITE_TACTIC = "decide +kernel"
const MAX_TERM_SIZE = 200_000
const MAX_SPECIALIZATIONS = 512

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
  return print(e, new Map())
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
  const script = tactic === undefined ? DEFAULT_TACTIC : tactic.includes("\n") ? "\n  " + tactic.trim().split("\n").join("\n  ") : tactic
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

function runFile(lean: string, source: string, directory: string, name: string): Promise<LeanMessage[]> {
  return new Promise((resolve, reject) => {
    const file = join(directory, name)
    writeFile(file, source).then(() => {
      execFile(lean, ["--json", file], { maxBuffer: 1 << 28 }, (error, stdout, stderr) => {
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

async function runChunk(lean: string, header: string, statements: string[], directory: string, name: string): Promise<LeanOutcome[]> {
  const lines = header.split("\n")
  const firstLine: number[] = []
  for (const [i, statement] of statements.entries()) {
    firstLine.push(lines.length + 1)
    lines.push(...`theorem c${i}${statement}`.split("\n"))
  }
  const messages = await runFile(lean, lines.join("\n") + "\n", directory, name)
  const outcomes: LeanOutcome[] = statements.map(() => ({ ok: true, message: "" }))
  for (const message of messages) {
    if (message.severity !== "error") continue
    const line = message.pos?.line ?? 0
    let index = -1
    for (let i = 0; i < firstLine.length && firstLine[i]! <= line; i++) index = i
    if (index < 0) throw new Error(`Lean rejected the generated preamble: ${message.data}`)
    const outcome = outcomes[index]!
    outcome.message = outcome.ok ? message.data : outcome.message + "\n" + message.data
    outcome.ok = false
  }
  return outcomes
}

/** Check each statement, in parallel across processes when there are many. */
export async function prove(lean: string, header: string, statements: string[]): Promise<LeanOutcome[]> {
  if (!statements.length) return []
  const directory = await mkdtemp(join(tmpdir(), "pudding-"))
  try {
    // Starting Lean costs little next to proving, so spread the work widely.
    const workers = Math.max(1, Math.min(availableParallelism(), Math.ceil(statements.length / 8)))
    const size = Math.ceil(statements.length / workers)
    const chunks: string[][] = []
    for (let i = 0; i < statements.length; i += size) chunks.push(statements.slice(i, i + size))
    const results = await Promise.all(chunks.map((chunk, i) => runChunk(lean, header, chunk, directory, `Proof${i}.lean`)))
    return results.flat()
  } finally {
    await rm(directory, { recursive: true, force: true })
  }
}

/** The Lean source for a set of statements, for inspection. */
export function render(header: string, statements: string[]): string {
  return header + "\n\n" + statements.map((statement, i) => `theorem c${i}${statement}`).join("\n\n") + "\n"
}
