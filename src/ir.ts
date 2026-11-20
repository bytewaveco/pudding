// The intermediate representation: first-order expressions over three scalar
// types. Everything structured (records, arrays, closures) is resolved by the
// translator before it reaches this level.

export type Ty = "bool" | "int" | "str"
export type Scalar = boolean | bigint | string

export type Op =
  | "not" | "and" | "or" | "eq" | "lt" | "le"
  | "add" | "sub" | "mul" | "neg" | "div" | "mod" | "fdiv"
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

export type ObligationKind = "expect" | "unreachable" | "falloff" | "missing" | "inherited" | "undefined" | "null" | "nothrow" | "overflow" | "nan" | "round"

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

const floorDivide = (a: bigint, b: bigint) => (a % b !== 0n && (a < 0n) !== (b < 0n) ? a / b - 1n : a / b)

/** Division rounded toward minus infinity, as `Math.floor(a / b)` computes it for whole numbers. The divisor must not be zero. */
export function fdiv(a: Expr, b: Expr): Expr {
  if (isLit(a) && isLit(b) && b.value !== 0n) return lit(floorDivide(a.value as bigint, b.value as bigint))
  if (isInt(b, 1n)) return a
  if (isInt(a, 0n)) return a
  return op("fdiv", "int", a, b)
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
    case "fdiv": return fdiv(a, b)
    case "concat": return concat(a, b)
    case "str": return toStr(a)
    case "ite": return ite(a, b, c)
  }
}

/** Replace variables by expressions, folding constants on the way back up. Iterative so deep DAGs never overflow the stack. */
export function substitute(root: Expr, values: ReadonlyMap<string, Expr>, memo = new Map<Expr, Expr>()): Expr {
  if (!values.size || root.t === "lit") return root
  if (root.t === "var") return values.get(root.name) ?? root
  const stack: [Expr, boolean][] = [[root, false]]
  while (stack.length) {
    const [e, expanded] = stack.pop()!
    if (e.t !== "op" || memo.has(e)) continue
    if (expanded) {
      let changed = false
      const args = e.args.map(arg => {
        const next = arg.t === "lit" ? arg : arg.t === "var" ? (values.get(arg.name) ?? arg) : memo.get(arg)!
        if (next !== arg) changed = true
        return next
      })
      memo.set(e, changed ? rebuild(e.op, args) : e)
    } else {
      stack.push([e, true])
      for (let i = e.args.length - 1; i >= 0; i--) {
        const arg = e.args[i]!
        if (arg.t === "op" && !memo.has(arg)) stack.push([arg, false])
      }
    }
  }
  return memo.get(root) ?? root
}

export function freeVariables(e: Expr, into = new Set<string>(), seen = new Set<Expr>()): Set<string> {
  const stack: Expr[] = [e]
  while (stack.length) {
    const cur = stack.pop()!
    if (cur.t === "var") into.add(cur.name)
    else if (cur.t === "op" && !seen.has(cur)) {
      seen.add(cur)
      for (const arg of cur.args) stack.push(arg)
    }
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

/** Number of distinct nodes in the expression DAG. */
export function dagSize(e: Expr, seen = new Set<Expr>()): number {
  let size = 0
  const stack: Expr[] = [e]
  while (stack.length) {
    const cur = stack.pop()!
    if (seen.has(cur)) continue
    seen.add(cur)
    size++
    if (cur.t === "op") for (const arg of cur.args) stack.push(arg)
  }
  return size
}

export function stringLiterals(e: Expr, into = new Set<string>(), seen = new Set<Expr>()): Set<string> {
  const stack: Expr[] = [e]
  while (stack.length) {
    const cur = stack.pop()!
    if (cur.t === "lit" && typeof cur.value === "string") into.add(cur.value)
    else if (cur.t === "op" && !seen.has(cur)) {
      seen.add(cur)
      for (const arg of cur.args) stack.push(arg)
    }
  }
  return into
}

export function integerLiterals(e: Expr, into = new Set<bigint>(), seen = new Set<Expr>()): Set<bigint> {
  const stack: Expr[] = [e]
  while (stack.length) {
    const cur = stack.pop()!
    if (cur.t === "lit" && typeof cur.value === "bigint") into.add(cur.value)
    else if (cur.t === "op" && !seen.has(cur)) {
      seen.add(cur)
      for (const arg of cur.args) stack.push(arg)
    }
  }
  return into
}

export class EvaluationError extends Error {}

/** Evaluate with JavaScript semantics. Iterative with lazy short-circuiting so deep DAGs never overflow the stack. */
export function evaluate(root: Expr, env: ReadonlyMap<string, Scalar>): Scalar {
  if (root.t === "lit") return root.value
  if (root.t === "var") return evalVar(env, root.name)
  const memo = new Map<Expr, Scalar>()
  const stack: { node: Expr; stage: number }[] = [{ node: root, stage: 0 }]
  const valueOf = (e: Expr): Scalar => (e.t === "lit" ? e.value : e.t === "var" ? evalVar(env, e.name) : memo.get(e)!)
  while (stack.length) {
    const frame = stack[stack.length - 1]!
    const e = frame.node
    if (e.t !== "op" || memo.has(e)) {
      stack.pop()
      continue
    }
    if (e.op === "and" || e.op === "or") {
      if (frame.stage === 0) {
        frame.stage = 1
        if (e.args[0]!.t === "op" && !memo.has(e.args[0]!)) stack.push({ node: e.args[0]!, stage: 0 })
      } else if (frame.stage === 1) {
        const left = valueOf(e.args[0]!)
        if ((e.op === "and" && !left) || (e.op === "or" && left)) {
          memo.set(e, left)
          stack.pop()
        } else {
          frame.stage = 2
          if (e.args[1]!.t === "op" && !memo.has(e.args[1]!)) stack.push({ node: e.args[1]!, stage: 0 })
        }
      } else {
        memo.set(e, valueOf(e.args[1]!))
        stack.pop()
      }
      continue
    }
    if (e.op === "ite") {
      if (frame.stage === 0) {
        frame.stage = 1
        if (e.args[0]!.t === "op" && !memo.has(e.args[0]!)) stack.push({ node: e.args[0]!, stage: 0 })
      } else if (frame.stage === 1) {
        const branch = valueOf(e.args[0]!) ? e.args[1]! : e.args[2]!
        frame.stage = 2
        if (branch.t === "op" && !memo.has(branch)) stack.push({ node: branch, stage: 0 })
      } else {
        const branch = valueOf(e.args[0]!) ? e.args[1]! : e.args[2]!
        memo.set(e, valueOf(branch))
        stack.pop()
      }
      continue
    }
    if (frame.stage === 0) {
      frame.stage = 1
      for (let i = e.args.length - 1; i >= 0; i--) {
        const arg = e.args[i]!
        if (arg.t === "op" && !memo.has(arg)) stack.push({ node: arg, stage: 0 })
      }
      continue
    }
    const a0 = valueOf(e.args[0]!)
    const a1 = e.args.length > 1 ? valueOf(e.args[1]!) : undefined
    let result: Scalar
    switch (e.op) {
      case "not": result = !a0; break
      case "eq": result = a0 === a1; break
      case "lt": result = (a0 as bigint) < (a1 as bigint); break
      case "le": result = (a0 as bigint) <= (a1 as bigint); break
      case "add": result = (a0 as bigint) + (a1 as bigint); break
      case "sub": result = (a0 as bigint) - (a1 as bigint); break
      case "mul": result = (a0 as bigint) * (a1 as bigint); break
      case "neg": result = -(a0 as bigint); break
      case "div": result = evalDiv(a0 as bigint, a1 as bigint); break
      case "mod": result = evalMod(a0 as bigint, a1 as bigint); break
      case "fdiv": result = evalFdiv(a0 as bigint, a1 as bigint); break
      case "concat": result = (a0 as string) + (a1 as string); break
      case "str": result = String(a0); break
    }
    memo.set(e, result)
    stack.pop()
  }
  return memo.get(root)!
}

function evalDiv(a: bigint, b: bigint): bigint {
  if (b === 0n) throw new EvaluationError("division by zero")
  return a / b
}

function evalMod(a: bigint, b: bigint): bigint {
  if (b === 0n) throw new EvaluationError("division by zero")
  return a % b
}

function evalFdiv(a: bigint, b: bigint): bigint {
  if (b === 0n) throw new EvaluationError("division by zero")
  return floorDivide(a, b)
}

function evalVar(env: ReadonlyMap<string, Scalar>, name: string): Scalar {
  const value = env.get(name)
  if (value === undefined) throw new EvaluationError(`unbound variable ${name}`)
  return value
}

/**
 * Compile an expression DAG into a direct JavaScript evaluator iteratively.
 * Shared nodes are wrapped in lazy memoized thunks (`tN ??= ...`), keeping
 * code size and evaluation time linear in the DAG while preserving exact
 * short-circuiting and division-by-zero exceptions. Deep expressions fall back
 * cleanly to the iterative evaluator so JS call stacks never overflow.
 */
export function compile(root: Expr): (env: ReadonlyMap<string, Scalar>) => Scalar {
  if (root.t === "lit") {
    const value = root.value
    return () => value
  }
  if (root.t === "var") {
    const name = root.name
    return env => evalVar(env, name)
  }
  const refs = new Map<Expr, number>()
  const visited = new Set<Expr>()
  const postorder: Expr[] = []
  const stack: [Expr, boolean][] = [[root, false]]
  while (stack.length) {
    const [e, expanded] = stack.pop()!
    if (e.t !== "op") continue
    if (expanded) {
      postorder.push(e)
      continue
    }
    refs.set(e, (refs.get(e) ?? 0) + 1)
    if (!visited.has(e)) {
      visited.add(e)
      stack.push([e, true])
      for (let i = e.args.length - 1; i >= 0; i--) stack.push([e.args[i]!, false])
    }
  }
  // Very deep thunk chains can still overflow the V8 call stack when invoked; use the iterative evaluator for those.
  if (postorder.length > 500) return env => evaluate(root, env)
  const exprs = new Map<Expr, string>()
  const defs: string[] = []
  let totalLength = 0
  const refOf = (e: Expr): string =>
    e.t === "lit" ? (typeof e.value === "bigint" ? (e.value < 0n ? `(${e.value}n)` : `${e.value}n`) : JSON.stringify(e.value))
      : e.t === "var" ? `v(env,${JSON.stringify(e.name)})` : exprs.get(e)!
  for (const e of postorder) {
    if (e.t !== "op") continue
    const a = e.args.map(refOf)
    let code: string
    switch (e.op) {
      case "not": code = `(!${a[0]})`; break
      case "and": code = `(${a[0]}&&${a[1]})`; break
      case "or": code = `(${a[0]}||${a[1]})`; break
      case "eq": code = `(${a[0]}===${a[1]})`; break
      case "lt": code = `(${a[0]}<${a[1]})`; break
      case "le": code = `(${a[0]}<=${a[1]})`; break
      case "add": code = `(${a[0]} + ${a[1]})`; break
      case "sub": code = `(${a[0]} - ${a[1]})`; break
      case "mul": code = `(${a[0]} * ${a[1]})`; break
      case "neg": code = `(-(${a[0]}))`; break
      case "div": code = `d(${a[0]},${a[1]})`; break
      case "mod": code = `m(${a[0]},${a[1]})`; break
      case "fdiv": code = `f(${a[0]},${a[1]})`; break
      case "concat": code = `(${a[0]} + ${a[1]})`; break
      case "str": code = `String(${a[0]})`; break
      case "ite": code = `(${a[0]}?${a[1]}:${a[2]})`; break
    }
    if ((refs.get(e) ?? 0) > 1 && e !== root) {
      const id = defs.length
      const def = `let t${id};const g${id}=()=>t${id}??=${code};`
      totalLength += def.length
      if (totalLength > 100_000) return env => evaluate(root, env)
      defs.push(def)
      exprs.set(e, `g${id}()`)
    } else {
      if (code.length > 100_000) return env => evaluate(root, env)
      exprs.set(e, code)
    }
  }
  const source = `${defs.join("")}return ${exprs.get(root)!}`
  if (source.length > 120_000) return env => evaluate(root, env)
  return new Function("v", "d", "m", "f", `return (env)=>{${source}}`)(evalVar, evalDiv, evalMod, evalFdiv) as (env: ReadonlyMap<string, Scalar>) => Scalar
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
