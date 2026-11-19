// The intermediate representation: first-order expressions over three scalar
// types. Everything structured (records, arrays, closures) is resolved by the
// translator before it reaches this level.

export type Ty = "bool" | "int" | "str"
export type Scalar = boolean | bigint | string

export type Op =
  | "not" | "and" | "or" | "eq" | "lt" | "le"
  | "add" | "sub" | "mul" | "neg" | "div" | "mod"
  | "concat" | "str" | "ite"

export type Expr =
  | { readonly t: "var"; readonly ty: Ty; readonly name: string }
  | { readonly t: "lit"; readonly ty: Ty; readonly value: Scalar }
  | { readonly t: "op"; readonly ty: Ty; readonly op: Op; readonly args: readonly Expr[] }

export interface Binder {
  /** Name of the variable in the IR and in Lean. */
  name: string
  /** How the input is written in the law, such as `from` or `entry.amount`. */
  label: string
  ty: Ty
  /** Present when the input ranges over a finite set of values. */
  domain?: Scalar[]
  /** True when the input is a JavaScript `number` holding a whole number, modeled as an integer. */
  num?: boolean
  /** Inclusive bounds of an integer input that is not enumerated. */
  range?: [bigint, bigint]
}

export type ObligationKind = "expect" | "unreachable" | "falloff" | "nothrow" | "overflow" | "nan"

export interface Obligation {
  kind: ObligationKind
  /** The condition under which the claim must hold. */
  guard: Expr
  claim: Expr
  file: string
  line: number
  column: number
  /** Source text of the statement that produced the obligation. */
  text: string
  /** Both sides of an equality assertion, kept for reporting. */
  sides?: { actual: Expr; expected: Expr; negated: boolean; num: boolean }
}

export const TRUE: Expr = { t: "lit", ty: "bool", value: true }
export const FALSE: Expr = { t: "lit", ty: "bool", value: false }

export function lit(value: Scalar): Expr {
  if (value === true) return TRUE
  if (value === false) return FALSE
  return { t: "lit", ty: typeof value === "bigint" ? "int" : "str", value }
}

export function variable(name: string, ty: Ty): Expr {
  return { t: "var", ty, name }
}

function isLit(e: Expr): e is Extract<Expr, { t: "lit" }> {
  return e.t === "lit"
}

export function same(a: Expr, b: Expr): boolean {
  if (a === b) return true
  if (a.t !== b.t || a.ty !== b.ty) return false
  if (a.t === "var") return a.name === (b as typeof a).name
  if (a.t === "lit") return a.value === (b as typeof a).value
  const other = b as typeof a
  return a.op === other.op && a.args.length === other.args.length && a.args.every((x, i) => same(x, other.args[i]!))
}

function op(o: Op, ty: Ty, ...args: Expr[]): Expr {
  return { t: "op", ty, op: o, args }
}

export function not(a: Expr): Expr {
  if (isLit(a)) return lit(!a.value)
  if (a.t === "op" && a.op === "not") return a.args[0]!
  return op("not", "bool", a)
}

export function and(a: Expr, b: Expr): Expr {
  if (isLit(a)) return a.value ? b : FALSE
  if (isLit(b)) return b.value ? a : FALSE
  if (same(a, b)) return a
  return op("and", "bool", a, b)
}

export function or(a: Expr, b: Expr): Expr {
  if (isLit(a)) return a.value ? TRUE : b
  if (isLit(b)) return b.value ? TRUE : a
  if (same(a, b)) return a
  return op("or", "bool", a, b)
}

export function all(parts: readonly Expr[]): Expr {
  return parts.reduce(and, TRUE)
}

export function eq(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b)) return lit(a.value === b.value)
  if (same(a, b)) return TRUE
  if (a.ty === "bool") {
    if (isLit(b)) return b.value ? a : not(a)
    if (isLit(a)) return a.value ? b : not(b)
  }
  return op("eq", "bool", a, b)
}

export function lt(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b)) return lit((a.value as bigint) < (b.value as bigint))
  if (same(a, b)) return FALSE
  return op("lt", "bool", a, b)
}

export function le(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b)) return lit((a.value as bigint) <= (b.value as bigint))
  if (same(a, b)) return TRUE
  return op("le", "bool", a, b)
}

const isInt = (e: Expr, n: bigint) => isLit(e) && e.value === n

export function add(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b)) return lit((a.value as bigint) + (b.value as bigint))
  if (isInt(a, 0n)) return b
  if (isInt(b, 0n)) return a
  return op("add", "int", a, b)
}

export function sub(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b)) return lit((a.value as bigint) - (b.value as bigint))
  if (isInt(b, 0n)) return a
  if (same(a, b)) return lit(0n)
  return op("sub", "int", a, b)
}

export function mul(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b)) return lit((a.value as bigint) * (b.value as bigint))
  if (isInt(a, 1n)) return b
  if (isInt(b, 1n)) return a
  if (isInt(a, 0n) || isInt(b, 0n)) return lit(0n)
  return op("mul", "int", a, b)
}

export function neg(a: Expr): Expr {
  if (isLit(a)) return lit(-(a.value as bigint))
  return op("neg", "int", a)
}

/** BigInt division, which truncates toward zero. The divisor must not be zero. */
export function div(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b) && b.value !== 0n) return lit((a.value as bigint) / (b.value as bigint))
  if (isInt(b, 1n)) return a
  // Zero divided by anything is zero; a zero divisor is ruled out separately.
  if (isInt(a, 0n)) return a
  return op("div", "int", a, b)
}

/** BigInt remainder, which takes the sign of the dividend. */
export function mod(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b) && b.value !== 0n) return lit((a.value as bigint) % (b.value as bigint))
  if (isInt(a, 0n)) return a
  return op("mod", "int", a, b)
}

/** String concatenation, kept flat and left-nested with adjacent literals merged so equal strings look equal. */
export function concat(a: Expr, b: Expr): Expr {
  const parts: Expr[] = []
  const collect = (e: Expr) => {
    if (e.t === "op" && e.op === "concat") e.args.forEach(collect)
    else if (isLit(e)) {
      const last = parts.at(-1)
      if (e.value === "") return
      if (last && isLit(last)) parts[parts.length - 1] = lit((last.value as string) + (e.value as string))
      else parts.push(e)
    } else parts.push(e)
  }
  collect(a)
  collect(b)
  if (!parts.length) return lit("")
  return parts.reduce((left, right) => op("concat", "str", left, right))
}

/** The decimal text of a bigint, as `String(n)` gives it. */
export function toStr(a: Expr): Expr {
  if (isLit(a)) return lit(String(a.value))
  return op("str", "str", a)
}

export function ite(c: Expr, a: Expr, b: Expr): Expr {
  if (isLit(c)) return c.value ? a : b
  if (same(a, b)) return a
  if (a.ty === "bool") {
    if (isLit(a) && isLit(b)) return a.value ? c : not(c)
    if (isLit(a)) return a.value ? or(c, b) : and(not(c), b)
    if (isLit(b)) return b.value ? or(not(c), a) : and(c, a)
  }
  return op("ite", a.ty, c, a, b)
}

function rebuild(o: Op, args: Expr[]): Expr {
  const [a, b, c] = args as [Expr, Expr, Expr]
  switch (o) {
    case "not": return not(a)
    case "and": return and(a, b)
    case "or": return or(a, b)
    case "eq": return eq(a, b)
    case "lt": return lt(a, b)
    case "le": return le(a, b)
    case "add": return add(a, b)
    case "sub": return sub(a, b)
    case "mul": return mul(a, b)
    case "neg": return neg(a)
    case "div": return div(a, b)
    case "mod": return mod(a, b)
    case "concat": return concat(a, b)
    case "str": return toStr(a)
    case "ite": return ite(a, b, c)
  }
}

/** Replace variables by expressions, folding constants on the way back up. */
export function substitute(e: Expr, values: ReadonlyMap<string, Expr>, memo = new Map<Expr, Expr>()): Expr {
  if (e.t === "lit") return e
  if (e.t === "var") return values.get(e.name) ?? e
  const seen = memo.get(e)
  if (seen) return seen
  let changed = false
  const args = e.args.map(arg => {
    const next = substitute(arg, values, memo)
    if (next !== arg) changed = true
    return next
  })
  const result = changed ? rebuild(e.op, args) : e
  memo.set(e, result)
  return result
}

export function freeVariables(e: Expr, into = new Set<string>(), seen = new Set<Expr>()): Set<string> {
  if (e.t === "var") into.add(e.name)
  else if (e.t === "op" && !seen.has(e)) {
    seen.add(e)
    for (const arg of e.args) freeVariables(arg, into, seen)
  }
  return into
}

/** Size of the expression when printed as a tree. */
export function treeSize(e: Expr, memo = new Map<Expr, number>()): number {
  if (e.t !== "op") return 1
  const seen = memo.get(e)
  if (seen !== undefined) return seen
  let size = 1
  for (const arg of e.args) size += treeSize(arg, memo)
  memo.set(e, size)
  return size
}

export function stringLiterals(e: Expr, into = new Set<string>(), seen = new Set<Expr>()): Set<string> {
  if (e.t === "lit" && typeof e.value === "string") into.add(e.value)
  else if (e.t === "op" && !seen.has(e)) {
    seen.add(e)
    for (const arg of e.args) stringLiterals(arg, into, seen)
  }
  return into
}

export class EvaluationError extends Error {}

/** Evaluate with JavaScript semantics. Only used for diagnostics, never to accept a law. */
export function evaluate(e: Expr, env: ReadonlyMap<string, Scalar>): Scalar {
  if (e.t === "lit") return e.value
  if (e.t === "var") {
    const value = env.get(e.name)
    if (value === undefined) throw new EvaluationError(`unbound variable ${e.name}`)
    return value
  }
  const arg = (i: number) => evaluate(e.args[i]!, env)
  switch (e.op) {
    case "not": return !arg(0)
    case "and": return arg(0) && arg(1)
    case "or": return arg(0) || arg(1)
    case "eq": return arg(0) === arg(1)
    case "lt": return (arg(0) as bigint) < (arg(1) as bigint)
    case "le": return (arg(0) as bigint) <= (arg(1) as bigint)
    case "add": return (arg(0) as bigint) + (arg(1) as bigint)
    case "sub": return (arg(0) as bigint) - (arg(1) as bigint)
    case "mul": return (arg(0) as bigint) * (arg(1) as bigint)
    case "neg": return -(arg(0) as bigint)
    case "div":
    case "mod": {
      const divisor = arg(1) as bigint
      if (divisor === 0n) throw new EvaluationError("division by zero")
      return e.op === "div" ? (arg(0) as bigint) / divisor : (arg(0) as bigint) % divisor
    }
    case "concat": return (arg(0) as string) + (arg(1) as string)
    case "str": return String(arg(0))
    case "ite": return arg(0) ? arg(1) : arg(2)
  }
}

/** A value as it is written in TypeScript. `num` marks an integer that stands for a `number`. */
export function showScalar(value: Scalar, num = false): string {
  return typeof value === "bigint" ? (num ? String(value) : `${value}n`) : JSON.stringify(value)
}

/** The largest whole number a JavaScript `number` holds exactly. */
export const MAX_SAFE = 2n ** 53n - 1n

/** Whether an integer is one a `number` holds exactly. */
export function isSafe(e: Expr): Expr {
  return and(le(lit(-MAX_SAFE), e), le(e, lit(MAX_SAFE)))
}
