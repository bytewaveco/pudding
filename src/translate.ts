// Translate law files into proof obligations by evaluating the TypeScript
// symbolically. Functions are inlined at their call sites, records and arrays
// are resolved here, and anything outside the supported subset is refused at
// the exact node instead of being approximated.

import { ElementFlags, SignatureKind, SymbolFlags, TypeFlags, type Checker, type Program, type Type } from "typescript/unstable/sync"
import { NodeFlags, SyntaxKind as K, type Node, type SourceFile } from "typescript/unstable/ast"
import * as ir from "./ir.ts"
import type { Binder, Expr, Obligation, ObligationKind, Scalar, Ty } from "./ir.ts"

// The compiler's node types are precise but verbose; the translator checks
// `kind` before every access, so nodes are handled untyped here.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type N = any

export interface Location {
  file: string
  line: number
  column: number
}

export class Unsupported extends Error {
  readonly node: Node | undefined
  constructor(message: string, node?: Node) {
    super(message)
    this.node = node
  }
}

/** How to build the runtime argument of a law callback from its inputs. */
export type ArgShape =
  | { k: "binder"; name: string }
  | { k: "const"; value: Scalar }
  | { k: "record"; fields: [string, ArgShape][] }
  | { k: "array"; items: ArgShape[] }

export interface LawInstance {
  binders: Binder[]
  arg: ArgShape | undefined
  obligations: Obligation[]
}

export interface Law {
  name: string
  file: string
  line: number
  column: number
  /** Position among the `law()` calls of the file. */
  index: number
  /** A Lean tactic script supplied by the author for symbolic obligations. */
  proof: string | undefined
  /** One instance per alternative of a union-typed input. */
  instances: LawInstance[]
  /** Every `expect()` in the law, keyed by `line:column`. */
  expectSites: Map<string, { line: number; column: number; text: string }>
  /** Set when the law could not be translated. */
  problem: ({ kind: "unsupported" | "invalid"; message: string } & Location) | undefined
}

type Value =
  | { k: "scalar"; e: Expr }
  | { k: "record"; fields: Map<string, Value> }
  | { k: "array"; items: Value[] }
  | { k: "closure"; node: N; env: Env }
  | { k: "choice"; cond: Expr; a: Value; b: Value }
  | { k: "bottom" }

type Shape =
  | { k: "scalar"; ty: Ty; values?: Scalar[] }
  | { k: "record"; fields: [string, Shape][] }
  | { k: "tuple"; items: Shape[] }
  | { k: "union"; alts: Shape[] }

class Env {
  private readonly vars = new Map<string, Value>()
  private readonly parent: Env | undefined
  constructor(parent?: Env) {
    this.parent = parent
  }
  get(name: string): Value | undefined {
    return this.vars.get(name) ?? this.parent?.get(name)
  }
  set(name: string, value: Value) {
    this.vars.set(name, value)
  }
  child() {
    return new Env(this)
  }
}

const BOTTOM: Value = { k: "bottom" }
const scalar = (e: Expr): Value => ({ k: "scalar", e })
const MAX_ALTERNATIVES = 64
const MODULE_DECLARATIONS = new Set<number>([
  K.ImportDeclaration, K.ExportDeclaration, K.ExportAssignment, K.VariableStatement, K.FunctionDeclaration, K.ClassDeclaration,
  K.InterfaceDeclaration, K.TypeAliasDeclaration, K.EnumDeclaration, K.ModuleDeclaration, K.ImportEqualsDeclaration, K.EmptyStatement,
])
const ARRAY_MUTATORS = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin", "set", "delete", "clear", "add"])

export function locate(node: Node): Location {
  const file = node.getSourceFile()
  const at = file.getLineAndCharacterOfPosition(node.getStart(file))
  return { file: file.fileName, line: at.line + 1, column: at.character + 1 }
}

function sourceText(node: Node): string {
  const text = node.getText(node.getSourceFile()).replace(/\s+/g, " ")
  return text.length > 140 ? text.slice(0, 137) + "..." : text
}

function describe(value: Value): string {
  switch (value.k) {
    case "scalar": return { bool: "a boolean", int: "a bigint", str: "a string" }[value.e.ty]
    case "record": return "an object"
    case "array": return "an array"
    case "closure": return "a function"
    case "choice": return "a value that depends on a condition"
    case "bottom": return "a thrown error"
  }
}

export class Translator {
  /** Source files whose code was read while translating. */
  readonly reached = new Set<string>()
  private readonly checker: Checker
  private readonly program: Program
  private readonly moduleName: string
  private readonly constants = new Map<Node, Value>()
  private readonly mutationChecked = new Set<string>()
  private stack: N[] = []
  private pc: Expr[] = []
  private instance: LawInstance | undefined
  private names = { law: new Set<string>(), domain: new Set<string>(), expect: new Set<string>() }

  constructor(program: Program, checker: Checker, moduleName = "pudding") {
    this.program = program
    this.checker = checker
    this.moduleName = moduleName
  }

  translateFile(file: SourceFile): Law[] {
    this.reached.add(file.fileName)
    this.names = { law: new Set(), domain: new Set(), expect: new Set() }
    for (const statement of file.statements as readonly N[]) {
      if (statement.kind !== K.ImportDeclaration || statement.moduleSpecifier.text !== this.moduleName) continue
      const bindings = statement.importClause?.namedBindings
      if (bindings?.kind !== K.NamedImports) continue
      for (const element of bindings.elements) {
        const imported = (element.propertyName ?? element.name).text as "law" | "domain" | "expect"
        if (imported in this.names) this.names[imported].add(element.name.text)
      }
    }
    const laws: Law[] = []
    for (const statement of file.statements as readonly N[]) {
      if (statement.kind !== K.ExpressionStatement) continue
      const call = statement.expression
      if (this.isCallTo(call, this.names.law)) laws.push(this.translateLaw(call, laws.length))
      else {
        laws.push({
          name: sourceText(statement), ...locate(statement), index: -1, proof: undefined, instances: [], expectSites: new Map(),
          problem: { kind: "invalid", message: "only law() calls and declarations are allowed at the top level of a law file", ...locate(statement) },
        })
      }
    }
    return laws
  }

  private isCallTo(node: N, names: Set<string>): boolean {
    return node?.kind === K.CallExpression && node.expression.kind === K.Identifier && names.has(node.expression.text)
  }

  private translateLaw(call: N, index: number): Law {
    const args = call.arguments as N[]
    const law: Law = {
      name: sourceText(call), ...locate(call), index, proof: undefined, instances: [], expectSites: new Map(), problem: undefined,
    }
    const invalid = (message: string, node: Node) => {
      law.problem = { kind: "invalid", message, ...locate(node) }
      return law
    }
    const nameNode = args[0]
    if (nameNode?.kind !== K.StringLiteral && nameNode?.kind !== K.NoSubstitutionTemplateLiteral) return invalid("the first argument of law() must be a string literal", call)
    law.name = nameNode.text
    const hasDomain = this.isCallTo(args[1], this.names.domain)
    const callback = args[hasDomain ? 2 : 1]
    const options = args[hasDomain ? 3 : 2]
    if (callback?.kind !== K.ArrowFunction && callback?.kind !== K.FunctionExpression) return invalid("law() needs a callback", call)
    if (callback.parameters.length !== (hasDomain ? 1 : 0)) return invalid(hasDomain ? "the callback takes exactly one parameter" : "a law without a domain takes no parameter", callback)
    if (options) {
      if (options.kind !== K.ObjectLiteralExpression) return invalid("law() options must be an object literal", options)
      for (const property of options.properties as N[]) {
        const value = property.initializer
        if (property.kind !== K.PropertyAssignment || property.name.text !== "proof" ||
          (value.kind !== K.StringLiteral && value.kind !== K.NoSubstitutionTemplateLiteral)) return invalid("the only option is `proof`, a string literal holding a Lean tactic script", property)
        law.proof = value.text
      }
    }
    this.collectExpectSites(callback.body, law)
    try {
      let alternatives: Shape[] = [{ k: "tuple", items: [] }]
      if (hasDomain) {
        const typeNode = args[1].typeArguments?.[0]
        if (!typeNode) return invalid("domain<T>() needs a type argument", args[1])
        const type = this.checker.getTypeFromTypeNode(typeNode)
        if (!type) return invalid("the domain type could not be resolved", typeNode)
        alternatives = this.expand(this.shapeOf(type, typeNode), typeNode)
      }
      for (const alternative of alternatives) {
        const instance: LawInstance = { binders: [], arg: undefined, obligations: [] }
        this.instance = instance
        if (hasDomain) instance.arg = this.instantiate(alternative, instance)
        law.instances.push(instance)
      }
      for (const instance of law.instances) {
        this.instance = instance
        this.pc = []
        this.stack = []
        const env = new Env()
        if (instance.arg) this.bind(callback.parameters[0].name, this.valueOf(instance.arg), env, true)
        const body = callback.body
        if (body.kind === K.Block) this.execLaw(body.statements, 0, env, () => {})
        else this.expectStatement(body, env)
      }
      if (law.expectSites.size === 0) return invalid("the law contains no expect() assertion", callback)
    } catch (error) {
      if (!(error instanceof Unsupported)) throw error
      law.problem = { kind: "unsupported", message: error.message, ...locate(error.node ?? call) }
      for (const instance of law.instances) instance.obligations = []
    } finally {
      this.instance = undefined
    }
    return law
  }

  private collectExpectSites(node: N, law: Law) {
    const visit = (n: N) => {
      if (n.kind === K.CallExpression && this.isCallTo(n, this.names.expect)) {
        let statement = n
        while (statement.parent && statement.kind !== K.ExpressionStatement && statement !== node) statement = statement.parent
        const at = locate(statement)
        law.expectSites.set(`${at.line}:${at.column}`, { line: at.line, column: at.column, text: sourceText(statement) })
      }
      n.forEachChild(visit)
    }
    visit(node)
  }

  // ---------------------------------------------------------------- domains

  private shapeOf(type: Type, at: Node): Shape {
    const flags = type.flags
    const name = () => this.checker.typeToString(type)
    if (flags & TypeFlags.Boolean) return { k: "scalar", ty: "bool", values: [true, false] }
    if (flags & TypeFlags.BooleanLiteral) return { k: "scalar", ty: "bool", values: [name() === "true"] }
    if (flags & TypeFlags.BigInt) return { k: "scalar", ty: "int" }
    if (flags & TypeFlags.BigIntLiteral) return { k: "scalar", ty: "int", values: [BigInt(name().replace(/n$/, ""))] }
    if (flags & TypeFlags.String) return { k: "scalar", ty: "str" }
    if (flags & TypeFlags.StringLiteral) return { k: "scalar", ty: "str", values: [this.wellFormed(String((type as N).value), at)] }
    if (flags & (TypeFlags.Number | TypeFlags.NumberLiteral)) throw new Unsupported("`number` is not modeled because it is floating point; use bigint for quantities", at)
    if (type.isUnionType()) {
      const members = type.getTypes().map(member => this.shapeOf(member, at))
      if (members.every(m => m.k === "scalar" && m.values && m.ty === (members[0] as typeof m).ty)) {
        const values = [...new Set(members.flatMap(m => (m as { values: Scalar[] }).values))]
        return { k: "scalar", ty: (members[0] as { ty: Ty }).ty, values }
      }
      if (members.every(m => m.k !== "scalar")) return { k: "union", alts: members }
      throw new Unsupported(`the union type ${name()} mixes kinds of values that are not supported together`, at)
    }
    if (this.checker.isTupleType(type)) {
      const elementFlags = ((type as N).getTarget?.().elementFlags ?? (type as N).elementFlags ?? []) as number[]
      if (elementFlags.some(flag => flag !== ElementFlags.Required)) throw new Unsupported("optional and rest tuple elements are not supported", at)
      return { k: "tuple", items: this.checker.getTypeArguments(type as N).map(item => this.shapeOf(item, at)) }
    }
    if (this.checker.isArrayType(type)) throw new Unsupported("arrays of unknown length are not supported as inputs; use a tuple", at)
    if (flags & TypeFlags.Object) {
      if (this.checker.getSignaturesOfType(type, SignatureKind.Call).length) throw new Unsupported("functions are not supported as inputs", at)
      const fields: [string, Shape][] = []
      for (const property of this.checker.getPropertiesOfType(type)) {
        if (property.flags & SymbolFlags.Optional) throw new Unsupported(`optional property \`${property.name}\` is not supported in an input`, at)
        const propertyType = this.checker.getTypeOfSymbol(property)
        if (!propertyType) throw new Unsupported(`the type of \`${property.name}\` could not be resolved`, at)
        fields.push([property.name, this.shapeOf(propertyType, at)])
      }
      return { k: "record", fields }
    }
    throw new Unsupported(`inputs of type ${name()} are not supported`, at)
  }

  /** Split union alternatives so that each result has one fixed structure. */
  private expand(shape: Shape, at: Node): Shape[] {
    const product = (parts: Shape[][]): Shape[][] => parts.reduce<Shape[][]>(
      (rows, options) => {
        const next = rows.flatMap(row => options.map(option => [...row, option]))
        if (next.length > MAX_ALTERNATIVES) throw new Unsupported(`the input type has more than ${MAX_ALTERNATIVES} union alternatives`, at)
        return next
      }, [[]])
    switch (shape.k) {
      case "scalar": return [shape]
      case "union": return shape.alts.flatMap(alt => this.expand(alt, at))
      case "tuple": return product(shape.items.map(item => this.expand(item, at))).map(items => ({ k: "tuple", items }))
      case "record": return product(shape.fields.map(([, field]) => this.expand(field, at)))
        .map(row => ({ k: "record", fields: row.map((field, i) => [shape.fields[i]![0], field] as [string, Shape]) }))
    }
  }

  private instantiate(shape: Shape, instance: LawInstance): ArgShape {
    switch (shape.k) {
      case "scalar": {
        if (shape.values?.length === 1) return { k: "const", value: shape.values[0]! }
        const name = `x${instance.binders.length}`
        instance.binders.push({ name, label: name, ty: shape.ty, ...(shape.values ? { domain: shape.values } : {}) })
        return { k: "binder", name }
      }
      case "tuple": return { k: "array", items: shape.items.map(item => this.instantiate(item, instance)) }
      case "record": return { k: "record", fields: shape.fields.map(([key, field]) => [key, this.instantiate(field, instance)]) }
      case "union": throw new Error("unions are expanded before instantiation")
    }
  }

  private valueOf(arg: ArgShape): Value {
    switch (arg.k) {
      case "binder": {
        const binder = this.instance!.binders.find(b => b.name === arg.name)!
        return scalar(ir.variable(binder.name, binder.ty))
      }
      case "const": return scalar(ir.lit(arg.value))
      case "array": return { k: "array", items: arg.items.map(item => this.valueOf(item)) }
      case "record": return { k: "record", fields: new Map(arg.fields.map(([key, field]) => [key, this.valueOf(field)])) }
    }
  }

  private relabel(value: Value, path: string) {
    if (value.k === "scalar" && value.e.t === "var") {
      const binder = this.instance?.binders.find(b => b.name === (value.e as { name: string }).name)
      if (binder) binder.label = path
    } else if (value.k === "record") for (const [key, field] of value.fields) this.relabel(field, `${path}.${key}`)
    else if (value.k === "array") value.items.forEach((item, i) => this.relabel(item, `${path}[${i}]`))
  }

  // ------------------------------------------------------------- law bodies

  private execLaw(statements: readonly N[], i: number, env: Env, next: () => void): void {
    if (i >= statements.length) return next()
    const statement = statements[i]
    const rest = () => this.execLaw(statements, i + 1, env, next)
    switch (statement.kind) {
      case K.EmptyStatement: return rest()
      case K.VariableStatement:
        this.declare(statement, env)
        return rest()
      case K.FunctionDeclaration:
        env.set(statement.name.text, { k: "closure", node: statement, env })
        return rest()
      case K.ExpressionStatement:
        this.expectStatement(statement.expression, env)
        return rest()
      case K.ReturnStatement:
        if (statement.expression) throw new Unsupported("a law callback cannot return a value", statement)
        return
      case K.Block:
        return this.execLaw(statement.statements, 0, env.child(), rest)
      case K.IfStatement: {
        const cond = this.bool(statement.expression, env)
        const run = (branch: N | undefined, after: () => void) =>
          branch ? this.execLaw(branch.kind === K.Block ? branch.statements : [branch], 0, env.child(), after) : after()
        const exits = containsReturn(statement.thenStatement) || containsReturn(statement.elseStatement)
        const after = exits ? rest : () => {}
        if (cond.t === "lit") run(cond.value ? statement.thenStatement : statement.elseStatement, after)
        else {
          this.under(cond, () => run(statement.thenStatement, after))
          this.under(ir.not(cond), () => run(statement.elseStatement, after))
        }
        if (!exits) rest()
        return
      }
      default:
        throw new Unsupported("this statement is not supported in a law", statement)
    }
  }

  private expectStatement(node: N, env: Env) {
    const fail = () => new Unsupported("a statement in a law must be expect(actual).toEqual(expected), .toBe(expected), or the .not form of either", node)
    if (node.kind !== K.CallExpression || node.expression.kind !== K.PropertyAccessExpression || node.arguments.length !== 1) throw fail()
    const matcher = node.expression.name.text as string
    if (matcher !== "toEqual" && matcher !== "toBe") throw fail()
    let target = node.expression.expression
    let negated = false
    if (target.kind === K.PropertyAccessExpression && target.name.text === "not") {
      negated = true
      target = target.expression
    }
    if (!this.isCallTo(target, this.names.expect) || target.arguments.length !== 1) throw fail()
    const actual = this.evalExpr(target.arguments[0], env)
    const expected = this.evalExpr(node.arguments[0], env)
    if (matcher === "toBe" && (actual.k !== "scalar" || expected.k !== "scalar")) {
      throw new Unsupported("toBe compares identity, which is only modeled for booleans, bigints and strings; use toEqual", node)
    }
    const equal = this.equal(actual, expected, node)
    const sides = actual.k === "scalar" && expected.k === "scalar" ? { actual: actual.e, expected: expected.e, negated } : undefined
    this.emit("expect", negated ? ir.not(equal) : equal, node, sides)
  }

  private equal(a: Value, b: Value, at: Node): Expr {
    if (a.k === "bottom" || b.k === "bottom") return ir.FALSE
    if (a.k === "choice") return ir.ite(a.cond, this.equal(a.a, b, at), this.equal(a.b, b, at))
    if (b.k === "choice") return ir.ite(b.cond, this.equal(a, b.a, at), this.equal(a, b.b, at))
    if (a.k === "scalar" && b.k === "scalar") {
      if (a.e.ty !== b.e.ty) throw new Unsupported(`cannot compare ${describe(a)} with ${describe(b)}`, at)
      return ir.eq(a.e, b.e)
    }
    if (a.k === "array" && b.k === "array") {
      if (a.items.length !== b.items.length) return ir.FALSE
      return ir.all(a.items.map((item, i) => this.equal(item, b.items[i]!, at)))
    }
    if (a.k === "record" && b.k === "record") {
      if (a.fields.size !== b.fields.size || [...a.fields.keys()].some(key => !b.fields.has(key))) {
        throw new Unsupported("comparing objects that have different property names is not supported", at)
      }
      return ir.all([...a.fields].map(([key, field]) => this.equal(field, b.fields.get(key)!, at)))
    }
    throw new Unsupported(`cannot compare ${describe(a)} with ${describe(b)}`, at)
  }

  private emit(kind: ObligationKind, claim: Expr, node: Node, sides?: Obligation["sides"]) {
    const guard = ir.all(this.pc)
    if (guard.t === "lit" && guard.value === false) return
    if (kind !== "expect" && claim.t === "lit" && claim.value === true) return
    if (!this.instance) throw new Unsupported("this code can throw while a module is being initialized", node)
    this.instance.obligations.push({ kind, guard, claim, ...locate(node), text: sourceText(node), ...(sides ? { sides } : {}) })
  }

  private under<T>(cond: Expr, run: () => T): T {
    this.pc.push(cond)
    try {
      return run()
    } finally {
      this.pc.pop()
    }
  }

  private branch(cond: Expr, whenTrue: () => Value, whenFalse: () => Value): Value {
    if (cond.t === "lit") return cond.value ? whenTrue() : whenFalse()
    const a = this.under(cond, whenTrue)
    const b = this.under(ir.not(cond), whenFalse)
    return this.merge(cond, a, b)
  }

  private merge(cond: Expr, a: Value, b: Value): Value {
    if (a.k === "bottom") return b
    if (b.k === "bottom") return a
    if (a.k === "scalar" && b.k === "scalar" && a.e.ty === b.e.ty) return scalar(ir.ite(cond, a.e, b.e))
    if (a.k === "array" && b.k === "array" && a.items.length === b.items.length) {
      return { k: "array", items: a.items.map((item, i) => this.merge(cond, item, b.items[i]!)) }
    }
    if (a.k === "record" && b.k === "record" && a.fields.size === b.fields.size && [...a.fields.keys()].every(key => b.fields.has(key))) {
      return { k: "record", fields: new Map([...a.fields].map(([key, field]) => [key, this.merge(cond, field, b.fields.get(key)!)])) }
    }
    if (a.k === "closure" && b.k === "closure" && a.node === b.node && a.env === b.env) return a
    return { k: "choice", cond, a, b }
  }

  /** Apply an operation to a value, distributing over conditional values. */
  private over(value: Value, apply: (value: Value) => Value): Value {
    if (value.k === "choice") return this.branch(value.cond, () => this.over(value.a, apply), () => this.over(value.b, apply))
    return apply(value)
  }

  // ------------------------------------------------------------- functions

  private declare(statement: N, env: Env) {
    const list = statement.declarationList
    if (!(list.flags & NodeFlags.Const)) throw new Unsupported("only `const` declarations are supported", statement)
    for (const declaration of list.declarations as N[]) {
      if (!declaration.initializer) throw new Unsupported("a declaration needs an initializer", declaration)
      this.bind(declaration.name, this.evalExpr(declaration.initializer, env), env)
    }
  }

  private bind(pattern: N, value: Value, env: Env, label = false) {
    if (pattern.kind === K.Identifier) {
      env.set(pattern.text, value)
      if (label) this.relabel(value, pattern.text)
      return
    }
    if (pattern.kind === K.ArrayBindingPattern) {
      if (value.k !== "array") throw new Unsupported(`cannot destructure ${describe(value)} as an array`, pattern)
      ;(pattern.elements as N[]).forEach((element, i) => {
        if (element.kind === K.OmittedExpression) return
        if (element.dotDotDotToken || element.initializer) throw new Unsupported("rest elements and defaults are not supported in destructuring", element)
        const item = value.items[i]
        if (!item) throw new Unsupported("destructuring reads past the end of the array", element)
        this.bind(element.name, item, env, label)
      })
      return
    }
    if (pattern.kind === K.ObjectBindingPattern) {
      if (value.k !== "record") throw new Unsupported(`cannot destructure ${describe(value)} as an object`, pattern)
      for (const element of pattern.elements as N[]) {
        if (element.dotDotDotToken || element.initializer) throw new Unsupported("rest elements and defaults are not supported in destructuring", element)
        const key = element.propertyName ?? element.name
        if (key.kind !== K.Identifier && key.kind !== K.StringLiteral) throw new Unsupported("computed property names are not supported", element)
        const field = value.fields.get(key.text)
        if (!field) throw new Unsupported(`property \`${key.text}\` does not exist on this object`, element)
        this.bind(element.name, field, env, label)
      }
      return
    }
    throw new Unsupported("this binding pattern is not supported", pattern)
  }

  private call(fn: Value, args: Value[], at: N): Value {
    if (fn.k === "choice") return this.branch(fn.cond, () => this.call(fn.a, args, at), () => this.call(fn.b, args, at))
    if (fn.k !== "closure") throw new Unsupported(`cannot call ${describe(fn)}`, at)
    const node = fn.node
    if (this.stack.includes(node)) throw new Unsupported("recursive functions are not supported", at)
    if (node.asteriskToken || node.modifiers?.some((m: N) => m.kind === K.AsyncKeyword)) throw new Unsupported("async functions and generators are not supported", at)
    if (!node.body) throw new Unsupported("this function has no body to translate", at)
    const env = fn.env.child()
    ;(node.parameters as N[]).forEach((parameter, i) => {
      if (parameter.dotDotDotToken) throw new Unsupported("rest parameters are not supported", parameter)
      let value = args[i]
      if (!value) {
        if (!parameter.initializer) throw new Unsupported("a call must pass every parameter that has no default", at)
        value = this.evalExpr(parameter.initializer, env)
      }
      this.bind(parameter.name, value, env)
    })
    this.stack.push(node)
    try {
      if (node.body.kind !== K.Block) return this.evalExpr(node.body, env)
      // Reaching the end of the body returns undefined, which is not modeled.
      // Like a throw, it is allowed only where it is proved unreachable.
      return this.exec(node.body.statements, 0, env, () => {
        this.emit("falloff", ir.FALSE, node)
        return BOTTOM
      })
    } finally {
      this.stack.pop()
    }
  }

  private exec(statements: readonly N[], i: number, env: Env, next: () => Value): Value {
    if (i >= statements.length) return next()
    const statement = statements[i]
    const rest = () => this.exec(statements, i + 1, env, next)
    switch (statement.kind) {
      case K.EmptyStatement: return rest()
      case K.VariableStatement:
        this.declare(statement, env)
        return rest()
      case K.FunctionDeclaration:
        env.set(statement.name.text, { k: "closure", node: statement, env })
        return rest()
      case K.ReturnStatement:
        if (!statement.expression) throw new Unsupported("returning without a value is not supported", statement)
        return this.evalExpr(statement.expression, env)
      case K.ThrowStatement:
        this.emit("unreachable", ir.FALSE, statement)
        return BOTTOM
      case K.Block:
        return this.exec(statement.statements, 0, env.child(), rest)
      case K.IfStatement: {
        const run = (branch: N | undefined) => () =>
          branch ? this.exec(branch.kind === K.Block ? branch.statements : [branch], 0, env.child(), rest) : rest()
        return this.branch(this.bool(statement.expression, env), run(statement.thenStatement), run(statement.elseStatement))
      }
      case K.SwitchStatement: {
        const subject = this.scalarOf(this.evalExpr(statement.expression, env), statement.expression)
        const clauses = statement.caseBlock.clauses as N[]
        const bodyFrom = (start: number) => {
          const body: N[] = []
          for (const clause of clauses.slice(start)) {
            for (const inner of clause.statements as N[]) {
              if (inner.kind === K.BreakStatement) return this.exec(body, 0, env.child(), rest)
              body.push(inner)
            }
          }
          return this.exec(body, 0, env.child(), rest)
        }
        const from = (index: number): Value => {
          const clause = clauses[index]
          if (!clause) return rest()
          if (clause.kind === K.DefaultClause) {
            if (index !== clauses.length - 1) throw new Unsupported("`default` must be the last clause of a switch", clause)
            return bodyFrom(index)
          }
          const label = this.scalarOf(this.evalExpr(clause.expression, env), clause.expression)
          if (label.ty !== subject.ty) throw new Unsupported("a case label must have the type of the switch subject", clause)
          return this.branch(ir.eq(subject, label), () => bodyFrom(index), () => from(index + 1))
        }
        return from(0)
      }
      default:
        throw new Unsupported("this statement is not supported in a function", statement)
    }
  }

  // ----------------------------------------------------------- expressions

  private scalarOf(value: Value, at: Node, ty?: Ty): Expr {
    if (value.k !== "scalar") throw new Unsupported(`expected ${ty ? { bool: "a boolean", int: "a bigint", str: "a string" }[ty] : "a boolean, bigint or string"} here but found ${describe(value)}`, at)
    if (ty && value.e.ty !== ty) throw new Unsupported(`expected ${{ bool: "a boolean", int: "a bigint", str: "a string" }[ty]} here but found ${describe(value)}`, at)
    return value.e
  }

  private bool(node: N, env: Env): Expr {
    const value = this.evalExpr(node, env)
    if (value.k !== "scalar" || value.e.ty !== "bool") throw new Unsupported(`a condition must be a boolean; JavaScript truthiness of ${describe(value)} is not modeled`, node)
    return value.e
  }

  private wellFormed(text: string, at: Node): string {
    if (!text.isWellFormed()) throw new Unsupported("string literals with unpaired surrogates are not supported", at)
    return text
  }

  private evalExpr(node: N, env: Env): Value {
    switch (node.kind) {
      case K.ParenthesizedExpression:
      case K.AsExpression:
      case K.SatisfiesExpression:
      case K.NonNullExpression:
      case K.TypeAssertionExpression:
        return this.evalExpr(node.expression, env)
      case K.StringLiteral:
      case K.NoSubstitutionTemplateLiteral:
        return scalar(ir.lit(this.wellFormed(node.text, node)))
      case K.TrueKeyword: return scalar(ir.TRUE)
      case K.FalseKeyword: return scalar(ir.FALSE)
      case K.BigIntLiteral: return scalar(ir.lit(BigInt(node.text.replace(/n$/, "").replaceAll("_", ""))))
      case K.NumericLiteral:
        throw new Unsupported("`number` is not modeled because it is floating point; use bigint for quantities", node)
      case K.Identifier: return env.get(node.text) ?? this.global(node)
      case K.ArrowFunction:
      case K.FunctionExpression:
        return { k: "closure", node, env }
      case K.PrefixUnaryExpression: {
        if (node.operator === K.ExclamationToken) return scalar(ir.not(this.bool(node.operand, env)))
        if (node.operator === K.MinusToken) return scalar(ir.neg(this.scalarOf(this.evalExpr(node.operand, env), node.operand, "int")))
        throw new Unsupported("this operator is not supported", node)
      }
      case K.ConditionalExpression:
        return this.branch(this.bool(node.condition, env), () => this.evalExpr(node.whenTrue, env), () => this.evalExpr(node.whenFalse, env))
      case K.BinaryExpression: return this.binary(node, env)
      case K.TemplateExpression: {
        let result = ir.lit(this.wellFormed(node.head.text, node))
        for (const span of node.templateSpans as N[]) {
          const part = this.evalExpr(span.expression, env)
          if (part.k !== "scalar" || part.e.ty !== "str") throw new Unsupported(`only strings can be interpolated, but this is ${describe(part)}`, span.expression)
          result = ir.concat(ir.concat(result, part.e), ir.lit(this.wellFormed(span.literal.text, span)))
        }
        return scalar(result)
      }
      case K.ObjectLiteralExpression: {
        const fields = new Map<string, Value>()
        for (const property of node.properties as N[]) {
          if (property.kind === K.SpreadAssignment) {
            const spread = this.evalExpr(property.expression, env)
            if (spread.k !== "record") throw new Unsupported(`cannot spread ${describe(spread)} into an object`, property)
            for (const [key, field] of spread.fields) fields.set(key, field)
          } else if (property.kind === K.ShorthandPropertyAssignment) {
            fields.set(property.name.text, env.get(property.name.text) ?? this.global(property.name, true))
          } else if (property.kind === K.PropertyAssignment && (property.name.kind === K.Identifier || property.name.kind === K.StringLiteral)) {
            fields.set(property.name.text, this.evalExpr(property.initializer, env))
          } else throw new Unsupported("methods, accessors and computed property names are not supported in object literals", property)
        }
        return { k: "record", fields }
      }
      case K.ArrayLiteralExpression: {
        const items: Value[] = []
        for (const element of node.elements as N[]) {
          if (element.kind === K.SpreadElement) {
            const spread = this.evalExpr(element.expression, env)
            if (spread.k !== "array") throw new Unsupported(`cannot spread ${describe(spread)} into an array`, element)
            items.push(...spread.items)
          } else if (element.kind === K.OmittedExpression) throw new Unsupported("array holes are not supported", node)
          else items.push(this.evalExpr(element, env))
        }
        return { k: "array", items }
      }
      case K.PropertyAccessExpression: {
        if (node.questionDotToken) throw new Unsupported("optional chaining is not supported", node)
        if (this.isNamespace(node.expression, env)) return this.global(node.name)
        const name = node.name.text as string
        return this.over(this.evalExpr(node.expression, env), object => {
          if (object.k === "bottom") return BOTTOM
          if (object.k !== "record") throw new Unsupported(`reading \`.${name}\` of ${describe(object)} is not supported`, node)
          const field = object.fields.get(name)
          if (!field) throw new Unsupported(`property \`${name}\` does not exist on this object`, node)
          return field
        })
      }
      case K.ElementAccessExpression: return this.elementAccess(node, env)
      case K.CallExpression: return this.callExpression(node, env)
      default:
        throw new Unsupported("this expression is not supported", node)
    }
  }

  private binary(node: N, env: Env): Value {
    const operator = node.operatorToken.kind
    if (operator === K.AmpersandAmpersandToken || operator === K.BarBarToken) {
      const isAnd = operator === K.AmpersandAmpersandToken
      const left = this.bool(node.left, env)
      if (left.t === "lit" && left.value !== isAnd) return scalar(left)
      const right = this.under(isAnd ? left : ir.not(left), () => this.bool(node.right, env))
      return scalar(isAnd ? ir.and(left, right) : ir.or(left, right))
    }
    const leftValue = this.evalExpr(node.left, env)
    const rightValue = this.evalExpr(node.right, env)
    if (operator === K.EqualsEqualsEqualsToken || operator === K.ExclamationEqualsEqualsToken) {
      if (leftValue.k !== "scalar" || rightValue.k !== "scalar") throw new Unsupported("=== is only modeled for booleans, bigints and strings", node)
      if (leftValue.e.ty !== rightValue.e.ty) throw new Unsupported(`cannot compare ${describe(leftValue)} with ${describe(rightValue)}`, node)
      const equal = ir.eq(leftValue.e, rightValue.e)
      return scalar(operator === K.EqualsEqualsEqualsToken ? equal : ir.not(equal))
    }
    if (operator === K.EqualsEqualsToken || operator === K.ExclamationEqualsToken) throw new Unsupported("use === and !==; loose equality is not modeled", node)
    if (operator === K.PlusToken && leftValue.k === "scalar" && rightValue.k === "scalar" && leftValue.e.ty === "str" && rightValue.e.ty === "str") {
      return scalar(ir.concat(leftValue.e, rightValue.e))
    }
    const left = this.scalarOf(leftValue, node.left, "int")
    const right = this.scalarOf(rightValue, node.right, "int")
    switch (operator) {
      case K.PlusToken: return scalar(ir.add(left, right))
      case K.MinusToken: return scalar(ir.sub(left, right))
      case K.AsteriskToken: return scalar(ir.mul(left, right))
      case K.SlashToken:
      case K.PercentToken:
        this.emit("nothrow", ir.not(ir.eq(right, ir.lit(0n))), node)
        return scalar(operator === K.SlashToken ? ir.div(left, right) : ir.mod(left, right))
      case K.LessThanToken: return scalar(ir.lt(left, right))
      case K.LessThanEqualsToken: return scalar(ir.le(left, right))
      case K.GreaterThanToken: return scalar(ir.lt(right, left))
      case K.GreaterThanEqualsToken: return scalar(ir.le(right, left))
      default: throw new Unsupported("this operator is not supported", node)
    }
  }

  private elementAccess(node: N, env: Env): Value {
    if (node.questionDotToken) throw new Unsupported("optional chaining is not supported", node)
    const index = node.argumentExpression
    return this.over(this.evalExpr(node.expression, env), object => {
      if (object.k === "bottom") return BOTTOM
      if (object.k === "array") {
        if (index.kind !== K.NumericLiteral || !/^\d+$/.test(index.text)) throw new Unsupported("arrays can only be indexed by a literal position", node)
        const item = object.items[Number(index.text)]
        if (!item) throw new Unsupported("this index is past the end of the array", node)
        return item
      }
      if (object.k !== "record") throw new Unsupported(`indexing ${describe(object)} is not supported`, node)
      const key = this.scalarOf(this.evalExpr(index, env), index, "str")
      if (key.t === "lit") {
        const field = object.fields.get(key.value as string)
        if (!field) throw new Unsupported(`property \`${key.value}\` does not exist on this object`, node)
        return field
      }
      // A key that is only known by its type: every value it can take must be a property.
      const keyType = this.checker.getTypeAtLocation(index)
      const members = keyType?.isUnionType() ? keyType.getTypes() : keyType ? [keyType] : []
      const keys = members.map(member => (member.flags & TypeFlags.StringLiteral ? String((member as N).value) : undefined))
      if (!keys.length || keys.some(k => k === undefined || !object.fields.has(k))) {
        throw new Unsupported("this index is not known to be one of the object's property names", node)
      }
      const pick = (i: number): Value => i === keys.length - 1
        ? object.fields.get(keys[i]!)!
        : this.branch(ir.eq(key, ir.lit(keys[i]!)), () => object.fields.get(keys[i]!)!, () => pick(i + 1))
      return pick(0)
    })
  }

  private callExpression(node: N, env: Env): Value {
    if (node.questionDotToken) throw new Unsupported("optional chaining is not supported", node)
    const callee = node.expression
    const args = () => (node.arguments as N[]).map(argument => {
      if (argument.kind === K.SpreadElement) throw new Unsupported("spread arguments are not supported", argument)
      return this.evalExpr(argument, env)
    })
    if (callee.kind === K.PropertyAccessExpression && !this.isNamespace(callee.expression, env)) {
      const method = callee.name.text as string
      return this.over(this.evalExpr(callee.expression, env), receiver => {
        if (receiver.k === "bottom") return BOTTOM
        if (receiver.k === "array") return this.arrayMethod(receiver.items, method, args(), node)
        if (receiver.k === "record" && receiver.fields.has(method)) return this.call(receiver.fields.get(method)!, args(), node)
        throw new Unsupported(`calling \`.${method}\` on ${describe(receiver)} is not supported`, node)
      })
    }
    return this.call(this.evalExpr(callee, env), args(), node)
  }

  private arrayMethod(items: Value[], method: string, args: Value[], node: N): Value {
    const [first] = args
    if (!first || args.length !== 1) throw new Unsupported(`\`.${method}\` is supported with exactly one argument`, node)
    switch (method) {
      case "includes": {
        const needle = this.scalarOf(first, node)
        return scalar(items.map(item => {
          const element = this.scalarOf(item, node)
          if (element.ty !== needle.ty) throw new Unsupported("includes() needs elements of the type being searched for", node)
          return ir.eq(element, needle)
        }).reduce(ir.or, ir.FALSE))
      }
      case "some":
      case "every": {
        const results = items.map(item => this.scalarOf(this.call(first, [item], node), node, "bool"))
        return scalar(method === "some" ? results.reduce(ir.or, ir.FALSE) : results.reduce(ir.and, ir.TRUE))
      }
      case "map":
        return { k: "array", items: items.map(item => this.call(first, [item], node)) }
      default:
        throw new Unsupported(`the array method \`.${method}\` is not supported`, node)
    }
  }

  // ------------------------------------------------------- module bindings

  private isNamespace(node: N, env: Env): boolean {
    if (node.kind !== K.Identifier || env.get(node.text)) return false
    let symbol = this.checker.getSymbolAtLocation(node)
    if (symbol && symbol.flags & SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol)
    return !!symbol && (symbol.flags & (SymbolFlags.ValueModule | SymbolFlags.NamespaceModule)) !== 0
  }

  /** Resolve a name that is not a local variable to its module-level declaration. */
  private global(node: N, shorthand = false): Value {
    let symbol = shorthand ? this.checker.getShorthandAssignmentValueSymbol(node.parent) : this.checker.getSymbolAtLocation(node)
    if (symbol && symbol.flags & SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol)
    const declaration = symbol?.valueDeclaration?.resolve() as N
    if (!symbol || !declaration) throw new Unsupported(`\`${node.text}\` is not a value that can be translated`, node)
    const file = declaration.getSourceFile() as SourceFile
    if (file.isDeclarationFile || this.program.isSourceFileFromExternalLibrary(file)) {
      throw new Unsupported(`\`${node.text}\` comes from a declaration file or a library, so its code cannot be read`, node)
    }
    this.reached.add(file.fileName)
    if (declaration.kind === K.FunctionDeclaration) return { k: "closure", node: declaration, env: new Env() }
    if (declaration.kind === K.VariableDeclaration) {
      const list = declaration.parent
      const moduleLevel = list.kind === K.VariableDeclarationList && list.parent.kind === K.VariableStatement && list.parent.parent.kind === K.SourceFile
      if (!moduleLevel) throw new Unsupported(`\`${node.text}\` is a local variable that is not available here`, node)
      if (!(list.flags & NodeFlags.Const)) throw new Unsupported(`\`${node.text}\` is a mutable module variable`, node)
      if (declaration.name.kind !== K.Identifier || !declaration.initializer) throw new Unsupported(`the declaration of \`${node.text}\` is not supported`, node)
      const known = this.constants.get(declaration)
      if (known) return known
      const saved = { pc: this.pc, stack: this.stack, instance: this.instance }
      this.pc = []
      this.stack = []
      this.instance = undefined
      try {
        const value = this.evalExpr(declaration.initializer, new Env())
        if (value.k !== "scalar" && value.k !== "closure") this.assertNotMutated(file, declaration.name.text, node)
        this.constants.set(declaration, value)
        return value
      } finally {
        Object.assign(this, saved)
      }
    }
    throw new Unsupported(`\`${node.text}\` is declared in a way that is not supported (only functions and const values are)`, node)
  }

  /** Refuse module constants whose contents are visibly changed in the file that declares them. */
  private assertNotMutated(file: SourceFile, name: string, use: Node) {
    const key = `${file.fileName}\0${name}`
    if (this.mutationChecked.has(key)) return
    // Statements that run when the module loads could change the value in ways this scan cannot follow.
    const loose = (file.statements as readonly N[]).find(statement => !MODULE_DECLARATIONS.has(statement.kind))
    if (loose) {
      throw new Unsupported(`the module that declares \`${name}\` runs a statement at line ${locate(loose).line} when it loads, so the initial value of \`${name}\` cannot be assumed`, use)
    }
    const visit = (node: N) => {
      if (node.kind === K.Identifier && node.text === name) {
        let top = node
        while ((top.parent.kind === K.PropertyAccessExpression || top.parent.kind === K.ElementAccessExpression) && top.parent.expression === top) top = top.parent
        const parent = top.parent
        const assigned = parent.kind === K.BinaryExpression && parent.left === top &&
          parent.operatorToken.kind >= K.FirstAssignment && parent.operatorToken.kind <= K.LastAssignment
        const updated = (parent.kind === K.PrefixUnaryExpression || parent.kind === K.PostfixUnaryExpression) &&
          (parent.operator === K.PlusPlusToken || parent.operator === K.MinusMinusToken)
        const mutated = parent.kind === K.CallExpression && parent.expression === top &&
          top.kind === K.PropertyAccessExpression && ARRAY_MUTATORS.has(top.name.text)
        if (top !== node && (assigned || updated || mutated || parent.kind === K.DeleteExpression)) {
          const at = locate(parent)
          throw new Unsupported(`\`${name}\` is modified at line ${at.line} of its module, so its initial value cannot be assumed`, use)
        }
      }
      node.forEachChild(visit)
    }
    visit(file)
    this.mutationChecked.add(key)
  }
}

function containsReturn(node: N | undefined): boolean {
  if (!node) return false
  if (node.kind === K.ReturnStatement) return true
  if (node.kind === K.ArrowFunction || node.kind === K.FunctionExpression || node.kind === K.FunctionDeclaration) return false
  return node.forEachChild((child: N) => containsReturn(child) || undefined) === true
}
