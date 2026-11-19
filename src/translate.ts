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
  | { k: "const"; value: Scalar; num?: boolean }
  | { k: "record"; fields: [string, ArgShape][] }
  | { k: "array"; items: ArgShape[] }

export interface LawInstance {
  /** What is known about the inputs beyond their types, such as the bounds of an integer. */
  assumptions: Expr[]
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
  /** `skip` and `todo` laws are listed but not checked. */
  mode: "run" | "skip" | "todo"
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
  /** `num` marks an integer expression that stands for a `number` rather than a bigint. */
  | { k: "scalar"; e: Expr; num?: boolean }
  | { k: "record"; fields: Map<string, Value> }
  | { k: "array"; items: Value[] }
  | { k: "closure"; node: N; env: Env }
  | { k: "choice"; cond: Expr; a: Value; b: Value }
  /** The result of a path that throws. It never reaches a caller, so it merges away. */
  | { k: "bottom" }
  /** `undefined`, as returned by a function that returns nothing. */
  | { k: "void" }

type Shape =
  | { k: "scalar"; ty: Ty; values?: Scalar[]; num?: boolean; range?: [bigint, bigint] }
  | { k: "record"; fields: [string, Shape][] }
  | { k: "tuple"; items: Shape[] }
  | { k: "union"; alts: Shape[] }

/** A variable. Only variables that are reassigned somewhere are `mutable`. */
interface Cell {
  value: Value
  readonly mutable: boolean
}

class Env {
  private readonly vars = new Map<string, Cell>()
  private readonly parent: Env | undefined
  constructor(parent?: Env) {
    this.parent = parent
  }
  cell(name: string): Cell | undefined {
    return this.vars.get(name) ?? this.parent?.cell(name)
  }
  get(name: string): Value | undefined {
    return this.cell(name)?.value
  }
  set(name: string, value: Value, mutable = false): Cell {
    const cell = { value, mutable }
    this.vars.set(name, cell)
    return cell
  }
  child() {
    return new Env(this)
  }
  /** Names of the reassignable variables visible from here. */
  mutableNames(into = new Set<string>()): Set<string> {
    for (const [name, cell] of this.vars) if (cell.mutable) into.add(name)
    return this.parent ? this.parent.mutableNames(into) : into
  }
}

/** Where control goes when a statement list ends, breaks out of, or continues a loop. */
interface Flow {
  next: () => Value
  brk?: () => Value
  cont?: () => Value
}

const BOTTOM: Value = { k: "bottom" }
const VOID: Value = { k: "void" }
const MAX_STEPS = 200_000
const COMPOUND = new Map<number, number>([
  [K.PlusEqualsToken, K.PlusToken], [K.MinusEqualsToken, K.MinusToken], [K.AsteriskEqualsToken, K.AsteriskToken],
  [K.SlashEqualsToken, K.SlashToken], [K.PercentEqualsToken, K.PercentToken],
])
const scalar = (e: Expr, num = false): Value => (num ? { k: "scalar", e, num } : { k: "scalar", e })
const isNumber = (value: Value) => value.k === "scalar" && value.num === true
/** Integer inputs with at most this many values are enumerated instead of quantified. */
const MAX_ENUMERATED_RANGE = 256n
const MAX_ITERATIONS = 2_000
const NUMBER_HELP = "`number` covers fractions, NaN and infinities, which are not modeled; use `Integer` from pudding for whole numbers, or bigint"
const MAX_ALTERNATIVES = 64
const MODULE_DECLARATIONS = new Set<number>([
  K.ImportDeclaration, K.ExportDeclaration, K.ExportAssignment, K.VariableStatement, K.FunctionDeclaration, K.ClassDeclaration,
  K.InterfaceDeclaration, K.TypeAliasDeclaration, K.EnumDeclaration, K.ModuleDeclaration, K.ImportEqualsDeclaration, K.EmptyStatement,
])
const DECLARATIONS_WITHOUT_VALUE = new Set<number>([K.ImportDeclaration, K.InterfaceDeclaration, K.TypeAliasDeclaration, K.EmptyStatement])
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
    case "scalar": return value.num ? "a number" : { bool: "a boolean", int: "a bigint", str: "a string" }[value.e.ty]
    case "record": return "an object"
    case "array": return "an array"
    case "closure": return "a function"
    case "choice": return "a value that depends on a condition"
    case "bottom": return "a thrown error"
    case "void": return "nothing"
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
  /** Every reassignable variable that is live, so their values can be saved and merged around branches. */
  private cells: Cell[] = []
  /** For each function being evaluated, the names it assigns to anywhere in its body. */
  private assigned: Set<string>[] = []
  private steps = 0
  private readonly facts = new Map<Node, { assigned: Set<string>; mentioned: Set<string>; returnsValue: boolean }>()
  private instance: LawInstance | undefined
  private names = { law: new Set<string>(), domain: new Set<string>(), expect: new Set<string>(), describe: new Set<string>() }

  constructor(program: Program, checker: Checker, moduleName = "pudding") {
    this.program = program
    this.checker = checker
    this.moduleName = moduleName
  }

  /**
   * Translate every law of a file. `selected` decides by full name which laws
   * to check; the rest are reported as skipped without being read.
   */
  translateFile(file: SourceFile, selected: (name: string) => boolean = () => true): Law[] {
    this.reached.add(file.fileName)
    this.names = { law: new Set(), domain: new Set(), expect: new Set(), describe: new Set() }
    for (const statement of file.statements as readonly N[]) {
      if (statement.kind !== K.ImportDeclaration || statement.moduleSpecifier.text !== this.moduleName) continue
      const bindings = statement.importClause?.namedBindings
      if (bindings?.kind !== K.NamedImports) continue
      for (const element of bindings.elements) {
        const imported = (element.propertyName ?? element.name).text as "law" | "domain" | "expect" | "describe"
        if (imported in this.names) this.names[imported].add(element.name.text)
      }
    }
    const laws: (Law & { only?: boolean })[] = []
    this.translateBlock(file.statements as readonly N[], undefined, [], "run", laws, selected)
    // As in Vitest, `.only` narrows the file to the laws that carry it.
    if (laws.some(law => law.only)) for (const law of laws) if (!law.only && law.mode === "run") this.skip(law)
    return laws
  }

  private skip(law: Law) {
    law.mode = "skip"
    law.instances = []
    law.problem = undefined
  }

  /** The `law` or `describe` call a statement makes, with its `.skip`, `.only` or `.todo` modifier. */
  private testCall(node: N): { kind: "law" | "describe"; modifier: string | undefined } | undefined {
    if (node?.kind !== K.CallExpression) return undefined
    let callee = node.expression
    let modifier: string | undefined
    if (callee.kind === K.PropertyAccessExpression && callee.expression.kind === K.Identifier) {
      modifier = callee.name.text
      callee = callee.expression
    }
    if (callee.kind !== K.Identifier) return undefined
    const kind = this.names.law.has(callee.text) ? "law" : this.names.describe.has(callee.text) ? "describe" : undefined
    return kind && { kind, modifier }
  }

  /**
   * Walk the statements of a law file or of a `describe` callback. At the top
   * level, declarations are resolved on demand through the checker; inside
   * `describe` they are local, so they are evaluated into `env` as they appear.
   */
  private translateBlock(
    statements: readonly N[], env: Env | undefined, path: string[], mode: "run" | "skip" | "only",
    laws: (Law & { only?: boolean })[], selected: (name: string) => boolean,
  ) {
    const invalid = (statement: N, message: string) => laws.push({
      name: sourceText(statement), ...locate(statement), index: -1, mode: "run", proof: undefined, instances: [], expectSites: new Map(),
      problem: { kind: "invalid", message, ...locate(statement) },
    })
    for (const statement of statements) {
      if (statement.kind !== K.ExpressionStatement) {
        if (!env || DECLARATIONS_WITHOUT_VALUE.has(statement.kind)) continue
        try {
          if (statement.kind === K.VariableStatement) this.declare(statement, env)
          else if (statement.kind === K.FunctionDeclaration) env.set(statement.name.text, { k: "closure", node: statement, env })
          else invalid(statement, "only laws and declarations are allowed inside describe()")
        } catch (error) {
          if (!(error instanceof Unsupported)) throw error
          invalid(error.node ?? statement, error.message)
        }
        continue
      }
      const call = statement.expression
      const test = this.testCall(call)
      if (!test) {
        invalid(statement, "only law() and describe() calls and declarations are allowed in a law file")
        continue
      }
      const { modifier } = test
      if (modifier !== undefined && modifier !== "skip" && modifier !== "only" && !(modifier === "todo" && test.kind === "law")) {
        invalid(statement, `\`.${modifier}\` is not a modifier Pudding knows; use .skip, .only or .todo`)
        continue
      }
      const own = modifier === "skip" || mode === "skip" ? "skip" : modifier === "only" || mode === "only" ? "only" : "run"
      const nameNode = call.arguments[0]
      if (nameNode?.kind !== K.StringLiteral && nameNode?.kind !== K.NoSubstitutionTemplateLiteral) {
        invalid(statement, `the first argument of ${test.kind}() must be a string literal`)
        continue
      }
      if (test.kind === "describe") {
        const body = call.arguments[1]
        if ((body?.kind !== K.ArrowFunction && body?.kind !== K.FunctionExpression) || body.body.kind !== K.Block || body.parameters.length) {
          invalid(statement, "describe() takes a name and a callback with a block body")
          continue
        }
        this.translateBlock(body.body.statements, (env ?? new Env()).child(), [...path, nameNode.text], own, laws, selected)
        continue
      }
      const name = [...path, nameNode.text].join(" > ")
      const index = laws.filter(law => law.index >= 0).length
      if (modifier === "todo" || own === "skip" || !selected(name)) {
        laws.push({
          name, ...locate(call), index, mode: modifier === "todo" ? "todo" : "skip", proof: undefined, instances: [], expectSites: new Map(), problem: undefined,
        })
        continue
      }
      const law: Law & { only?: boolean } = this.translateLaw(call, index, name, env)
      if (own === "only") law.only = true
      laws.push(law)
    }
  }

  private isCallTo(node: N, names: Set<string>): boolean {
    return node?.kind === K.CallExpression && node.expression.kind === K.Identifier && names.has(node.expression.text)
  }

  private translateLaw(call: N, index: number, name: string, scope: Env | undefined): Law {
    const args = call.arguments as N[]
    const law: Law = {
      name, ...locate(call), index, mode: "run", proof: undefined, instances: [], expectSites: new Map(), problem: undefined,
    }
    const invalid = (message: string, node: Node) => {
      law.problem = { kind: "invalid", message, ...locate(node) }
      return law
    }
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
        const instance: LawInstance = { assumptions: [], binders: [], arg: undefined, obligations: [] }
        this.instance = instance
        if (hasDomain) instance.arg = this.instantiate(alternative, instance)
        law.instances.push(instance)
      }
      for (const instance of law.instances) {
        this.instance = instance
        this.pc = [...instance.assumptions]
        this.stack = []
        this.cells = []
        this.steps = 0
        this.assigned = [this.factsOf(callback).assigned]
        const env = scope ? scope.child() : new Env()
        if (instance.arg) this.bind(callback.parameters[0].name, this.valueOf(instance.arg), env, true, true)
        const body = callback.body
        if (body.kind === K.Block) this.exec(body.statements, 0, env, { next: () => VOID })
        else this.effect(body, env)
      }
      const asserts = law.expectSites.size > 0 || law.instances.some(instance => instance.obligations.some(o => o.kind === "expect"))
      if (!asserts) return invalid("the law contains no expect() assertion", callback)
    } catch (error) {
      if (!(error instanceof Unsupported)) throw error
      law.problem = { kind: "unsupported", message: error.message, ...locate(error.node ?? call) }
      for (const instance of law.instances) instance.obligations = []
    } finally {
      this.instance = undefined
      this.assigned = []
      this.cells = []
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
    if (flags & TypeFlags.NumberLiteral) {
      const value = Number((type as N).value)
      if (!Number.isSafeInteger(value)) throw new Unsupported(`the number ${name()} is not a whole number that can be held exactly`, at)
      return { k: "scalar", ty: "int", num: true, values: [BigInt(value)] }
    }
    if (flags & TypeFlags.Number) throw new Unsupported(NUMBER_HELP, at)
    if (type.isIntersectionType()) {
      // `Integer<Min, Max>` is `number` intersected with a marker that carries the bounds.
      const members = type.getTypes()
      const marker = members.map(member => this.checker.getPropertyOfType(member, "__puddingInteger")).find(Boolean)
      if (marker && members.some(member => member.flags & TypeFlags.Number)) {
        const carried = this.checker.getTypeOfSymbol(marker)
        const tuple = (carried?.isUnionType() ? carried.getTypes() : carried ? [carried] : []).find(member => this.checker.isTupleType(member))
        const bound = (member: Type | undefined, fallback: bigint) =>
          member && member.flags & TypeFlags.NumberLiteral && Number.isSafeInteger(Number((member as N).value)) ? BigInt(Number((member as N).value)) : fallback
        const [low, high] = tuple ? this.checker.getTypeArguments(tuple as N) : []
        const range: [bigint, bigint] = [bound(low, -ir.MAX_SAFE), bound(high, ir.MAX_SAFE)]
        if (range[0] > range[1]) throw new Unsupported(`${name()} has a lower bound above its upper bound`, at)
        if (range[1] - range[0] < MAX_ENUMERATED_RANGE) {
          const values: Scalar[] = []
          for (let value = range[0]; value <= range[1]; value++) values.push(value)
          return { k: "scalar", ty: "int", num: true, values }
        }
        return { k: "scalar", ty: "int", num: true, range }
      }
    }
    if (type.isUnionType()) {
      const members = type.getTypes().map(member => this.shapeOf(member, at))
      const first = members[0] as Extract<Shape, { k: "scalar" }>
      if (members.every(m => m.k === "scalar" && m.values && m.ty === first.ty && !!m.num === !!first.num)) {
        const values = [...new Set(members.flatMap(m => (m as { values: Scalar[] }).values))]
        return { k: "scalar", ty: first.ty, values, ...(first.num ? { num: true } : {}) }
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
        if (shape.values?.length === 1) return { k: "const", value: shape.values[0]!, ...(shape.num ? { num: true } : {}) }
        const name = `x${instance.binders.length}`
        instance.binders.push({
          name, label: name, ty: shape.ty,
          ...(shape.values ? { domain: shape.values } : {}), ...(shape.num ? { num: true } : {}), ...(shape.range ? { range: shape.range } : {}),
        })
        if (shape.range) {
          const input = ir.variable(name, "int")
          instance.assumptions.push(ir.and(ir.le(ir.lit(shape.range[0]), input), ir.le(input, ir.lit(shape.range[1]))))
        }
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
        return scalar(ir.variable(binder.name, binder.ty), binder.num)
      }
      case "const": return scalar(ir.lit(arg.value), arg.num)
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

  /** Whether a call is rooted in `expect(...)`, however the chain after it is written. */
  private startsWithExpect(node: N): boolean {
    let current = node
    while (current) {
      if (this.isCallTo(current, this.names.expect)) return true
      if (current.kind === K.CallExpression || current.kind === K.PropertyAccessExpression) current = current.expression
      else return false
    }
    return false
  }

  private expectStatement(node: N, env: Env) {
    const fail = () => new Unsupported("an assertion must be expect(actual).toEqual(expected), .toBe(expected), or the .not form of either", node)
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
    const sides = actual.k === "scalar" && expected.k === "scalar" ? { actual: actual.e, expected: expected.e, negated, num: !!actual.num } : undefined
    this.emit("expect", negated ? ir.not(equal) : equal, node, sides)
  }

  private equal(a: Value, b: Value, at: Node): Expr {
    if (a.k === "bottom" || b.k === "bottom") return ir.FALSE
    if (a.k === "choice") return ir.ite(a.cond, this.equal(a.a, b, at), this.equal(a.b, b, at))
    if (b.k === "choice") return ir.ite(b.cond, this.equal(a, b.a, at), this.equal(a, b.b, at))
    if (a.k === "scalar" && b.k === "scalar") {
      if (a.e.ty !== b.e.ty || !!a.num !== !!b.num) throw new Unsupported(`cannot compare ${describe(a)} with ${describe(b)}`, at)
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

  private save(): Value[] {
    return this.cells.map(cell => cell.value)
  }

  /** Put variables back to a saved state, forgetting any declared since. */
  private restore(saved: Value[]) {
    this.cells.length = saved.length
    this.cells.forEach((cell, i) => (cell.value = saved[i]!))
  }

  /**
   * Evaluate both sides of a condition and merge their results. Each side
   * starts from the same variable state. The state afterwards is the state
   * before: an expression cannot assign, and a statement branch evaluated
   * this way has already run to the end of its function on both sides.
   */
  private branch(cond: Expr, whenTrue: () => Value, whenFalse: () => Value): Value {
    if (cond.t === "lit") return cond.value ? whenTrue() : whenFalse()
    const before = this.save()
    const a = this.under(cond, whenTrue)
    this.restore(before)
    const b = this.under(ir.not(cond), whenFalse)
    this.restore(before)
    return this.merge(cond, a, b)
  }

  /**
   * Run two branches that both continue past the condition, then make every
   * variable hold the value of whichever branch was taken. The code after
   * the condition is then evaluated once, not once per branch.
   */
  private mergeStates(cond: Expr, whenTrue: () => void, whenFalse: () => void) {
    const before = this.save()
    this.under(cond, whenTrue)
    const afterTrue = this.save()
    this.restore(before)
    this.under(ir.not(cond), whenFalse)
    const afterFalse = this.save()
    this.restore(before)
    this.cells.forEach((cell, i) => {
      const a = afterTrue[i]!
      const b = afterFalse[i]!
      cell.value = a === b ? a : this.merge(cond, a, b)
    })
  }

  private merge(cond: Expr, a: Value, b: Value): Value {
    if (a.k === "bottom") return b
    if (b.k === "bottom") return a
    if (a.k === "scalar" && b.k === "scalar" && a.e.ty === b.e.ty && !!a.num === !!b.num) return scalar(ir.ite(cond, a.e, b.e), a.num)
    if (a.k === "array" && b.k === "array" && a.items.length === b.items.length) {
      return { k: "array", items: a.items.map((item, i) => this.merge(cond, item, b.items[i]!)) }
    }
    if (a.k === "record" && b.k === "record" && a.fields.size === b.fields.size && [...a.fields.keys()].every(key => b.fields.has(key))) {
      return { k: "record", fields: new Map([...a.fields].map(([key, field]) => [key, this.merge(cond, field, b.fields.get(key)!)])) }
    }
    if (a.k === "closure" && b.k === "closure" && a.node === b.node && a.env === b.env) return a
    if (a.k === "void" && b.k === "void") return a
    return { k: "choice", cond, a, b }
  }

  /** Apply an operation to a value, distributing over conditional values. */
  private over(value: Value, apply: (value: Value) => Value): Value {
    if (value.k === "choice") return this.branch(value.cond, () => this.over(value.a, apply), () => this.over(value.b, apply))
    return apply(value)
  }

  // ------------------------------------------------------------- functions

  /** What a function's body does that affects how it is evaluated, computed once per function. */
  private factsOf(fn: N) {
    let facts = this.facts.get(fn)
    if (facts) return facts
    facts = { assigned: new Set<string>(), mentioned: new Set<string>(), returnsValue: false }
    const isFunction = (node: N) => node.kind === K.ArrowFunction || node.kind === K.FunctionExpression || node.kind === K.FunctionDeclaration
    const visit = (node: N, nested: boolean) => {
      if (node.kind === K.Identifier) facts!.mentioned.add(node.text)
      if (node.kind === K.BinaryExpression && node.operatorToken.kind >= K.FirstAssignment && node.operatorToken.kind <= K.LastAssignment) {
        collectNames(node.left, facts!.assigned)
      }
      if ((node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
        (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)) collectNames(node.operand, facts!.assigned)
      if (node.kind === K.ReturnStatement && node.expression && !nested) facts!.returnsValue = true
      node.forEachChild((child: N) => visit(child, nested || isFunction(child)))
    }
    for (const parameter of fn.parameters as N[]) visit(parameter, false)
    if (fn.body) visit(fn.body, false)
    this.facts.set(fn, facts)
    return facts
  }

  private declare(statement: N, env: Env) {
    const list = statement.declarationList ?? statement
    const reassignable = (list.flags & NodeFlags.Let) !== 0
    if (!reassignable && !(list.flags & NodeFlags.Const)) throw new Unsupported("`var` is not supported; use `const` or `let`", statement)
    for (const declaration of list.declarations as N[]) {
      if (!declaration.initializer && !reassignable) throw new Unsupported("a declaration needs an initializer", declaration)
      // A `let` without an initializer holds nothing until it is assigned; TypeScript rejects reading it before then.
      this.bind(declaration.name, declaration.initializer ? this.evalExpr(declaration.initializer, env) : BOTTOM, env, false, reassignable)
    }
  }

  /**
   * Bind the names of a pattern. A name becomes a reassignable variable only
   * if the enclosing function assigns to it somewhere; everything else stays
   * an immutable binding, which keeps closures over it exact.
   */
  private bind(pattern: N, value: Value, env: Env, label = false, reassignable = false) {
    if (pattern.kind === K.Identifier) {
      const cell = env.set(pattern.text, value, reassignable && this.assigned.at(-1)?.has(pattern.text) === true)
      if (cell.mutable) this.cells.push(cell)
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
        this.bind(element.name, item, env, label, reassignable)
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
        this.bind(element.name, field, env, label, reassignable)
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
    const facts = this.factsOf(node)
    // A function that reads or writes a variable someone reassigns would need
    // that variable's value at the moment of the call, on every path. That is
    // not tracked, so such closures are refused.
    for (const name of fn.env.mutableNames()) {
      if (facts.mentioned.has(name)) throw new Unsupported(`this function uses \`${name}\`, a variable that is reassigned outside it; that is not modeled`, at)
    }
    const env = fn.env.child()
    const live = this.cells.length
    this.stack.push(node)
    this.assigned.push(facts.assigned)
    try {
      ;(node.parameters as N[]).forEach((parameter, i) => {
        if (parameter.dotDotDotToken) throw new Unsupported("rest parameters are not supported", parameter)
        let value = args[i]
        if (!value) {
          if (!parameter.initializer) throw new Unsupported("a call must pass every parameter that has no default", at)
          value = this.evalExpr(parameter.initializer, env)
        }
        this.bind(parameter.name, value, env, false, true)
      })
      if (node.body.kind !== K.Block) return this.evalExpr(node.body, env)
      // Reaching the end of a function that returns values elsewhere yields
      // undefined where a value is expected. Like a throw, that is allowed
      // only where it is proved unreachable.
      return this.exec(node.body.statements, 0, env, {
        next: () => {
          if (!facts.returnsValue) return VOID
          this.emit("falloff", ir.FALSE, node)
          return BOTTOM
        },
      })
    } finally {
      this.stack.pop()
      this.assigned.pop()
      this.cells.length = live
    }
  }

  /**
   * Evaluate statements from index `i`. `flow.next` continues after the list.
   * A branch that can leave early is evaluated together with everything that
   * follows it; a branch that cannot is evaluated alone and its variables are
   * merged, so straight-line code costs one pass.
   */
  private exec(statements: readonly N[], i: number, env: Env, flow: Flow): Value {
    if (i >= statements.length) return flow.next()
    const statement = statements[i]
    if (++this.steps > MAX_STEPS) throw new Unsupported("this code has too many paths to follow", statement)
    const rest = () => this.exec(statements, i + 1, env, flow)
    const after: Flow = { ...flow, next: rest }
    const run = (block: N | undefined, to: Flow): Value =>
      block ? this.exec(block.kind === K.Block ? block.statements : [block], 0, env.child(), to) : to.next()
    switch (statement.kind) {
      case K.EmptyStatement: return rest()
      case K.VariableStatement:
        this.declare(statement, env)
        return rest()
      case K.FunctionDeclaration:
        env.set(statement.name.text, { k: "closure", node: statement, env })
        return rest()
      case K.ExpressionStatement:
        this.effect(statement.expression, env)
        return rest()
      case K.ReturnStatement:
        return statement.expression ? this.evalExpr(statement.expression, env) : VOID
      case K.ThrowStatement:
        this.emit("unreachable", ir.FALSE, statement)
        return BOTTOM
      case K.BreakStatement:
      case K.ContinueStatement: {
        const target = statement.kind === K.BreakStatement ? flow.brk : flow.cont
        if (statement.label || !target) throw new Unsupported("this break or continue is not supported", statement)
        return target()
      }
      case K.Block:
        return run(statement, after)
      case K.IfStatement: {
        const cond = this.bool(statement.expression, env)
        if (cond.t === "lit") return run(cond.value ? statement.thenStatement : statement.elseStatement, after)
        if (canExit(statement.thenStatement) || canExit(statement.elseStatement)) {
          return this.branch(cond, () => run(statement.thenStatement, after), () => run(statement.elseStatement, after))
        }
        const stop: Flow = { next: () => VOID }
        this.mergeStates(cond, () => run(statement.thenStatement, stop), () => run(statement.elseStatement, stop))
        return rest()
      }
      case K.SwitchStatement: {
        const subject = this.scalarOf(this.evalExpr(statement.expression, env), statement.expression)
        const clauses = statement.caseBlock.clauses as N[]
        // Entering at a clause runs it and every clause below it until a break.
        const bodyFrom = (start: number) =>
          this.exec(clauses.slice(start).flatMap(clause => clause.statements as N[]), 0, env.child(), { ...flow, next: rest, brk: rest })
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
      case K.ForOfStatement: {
        const declarations = statement.initializer
        const declared = declarations.kind === K.VariableDeclarationList ? (declarations.declarations as N[]) : []
        const reassignable = (declarations.flags & NodeFlags.Let) !== 0
        if (statement.awaitModifier || declared.length !== 1 || declared[0].initializer || (!reassignable && !(declarations.flags & NodeFlags.Const))) {
          throw new Unsupported("a loop must be written `for (const item of items)`", statement)
        }
        // The loop is unrolled, so the array must have a length known here.
        return this.over(this.evalExpr(statement.expression, env), items => {
          if (items.k === "bottom") return BOTTOM
          if (items.k !== "array") throw new Unsupported(`a loop needs an array whose length is known here, but this is ${describe(items)}`, statement.expression)
          const iterate = (index: number): Value => {
            const item = items.items[index]
            if (!item) return rest()
            const scope = env.child()
            this.bind(declared[0].name, item, scope, false, reassignable)
            const onward = () => iterate(index + 1)
            const body = statement.statement
            return this.exec(body.kind === K.Block ? body.statements : [body], 0, scope, { next: onward, cont: onward, brk: rest })
          }
          return iterate(0)
        })
      }
      case K.WhileStatement:
      case K.DoStatement:
      case K.ForStatement: {
        // These loops are unrolled by running them: the condition must come
        // out as plainly true or false each time round, as it does when it
        // only depends on a counter and on lengths known here.
        const scope = env.child()
        const initializer = statement.kind === K.ForStatement ? statement.initializer : undefined
        if (initializer?.kind === K.VariableDeclarationList) this.declare(initializer, scope)
        else if (initializer) this.effect(initializer, scope)
        const condition = statement.kind === K.ForStatement ? statement.condition : statement.expression
        const body = statement.statement
        let rounds = 0
        const test = (): Value => {
          const cond = condition ? this.bool(condition, scope) : ir.TRUE
          if (cond.t !== "lit") throw new Unsupported("how many times this loop runs depends on a value that is not known here", condition)
          return cond.value ? round() : rest()
        }
        const step = (): Value => {
          if (statement.kind === K.ForStatement && statement.incrementor) this.effect(statement.incrementor, scope)
          return test()
        }
        const round = (): Value => {
          if (++rounds > MAX_ITERATIONS) throw new Unsupported(`this loop runs more than ${MAX_ITERATIONS} times, which is too many to unroll`, statement)
          return this.exec(body.kind === K.Block ? body.statements : [body], 0, scope.child(), { next: step, cont: step, brk: rest })
        }
        return statement.kind === K.DoStatement ? round() : test()
      }
      case K.ForInStatement:
        throw new Unsupported("for...in loops are not supported", statement)
      case K.TryStatement:
        throw new Unsupported("try, catch and finally are not supported", statement)
      default:
        throw new Unsupported("this statement is not supported", statement)
    }
  }

  /** A statement that is an expression: an assignment, an assertion, or a call made for the assertions inside it. */
  private effect(node: N, env: Env): void {
    if (node.kind === K.ParenthesizedExpression) return this.effect(node.expression, env)
    if (node.kind === K.BinaryExpression && node.operatorToken.kind >= K.FirstAssignment && node.operatorToken.kind <= K.LastAssignment) {
      const operator = node.operatorToken.kind
      const base = COMPOUND.get(operator)
      if (operator !== K.EqualsToken && base === undefined) throw new Unsupported("this assignment operator is not supported", node)
      const cell = this.assignable(node.left, env)
      // The right-hand side is evaluated first; it cannot change the variable, because closures over it are refused.
      const right = this.evalExpr(node.right, env)
      cell.value = base === undefined ? right : this.arithmetic(base, cell.value, right, node)
      return
    }
    if ((node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
      (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)) {
      const cell = this.assignable(node.operand, env)
      const one = scalar(ir.lit(1n), isNumber(cell.value))
      cell.value = this.arithmetic(node.operator === K.PlusPlusToken ? K.PlusToken : K.MinusToken, cell.value, one, node)
      return
    }
    if (node.kind === K.CallExpression) {
      if (this.startsWithExpect(node)) return this.expectStatement(node, env)
      this.evalExpr(node, env)
      return
    }
    throw new Unsupported("this statement does nothing that is modeled", node)
  }

  private assignable(target: N, env: Env): Cell {
    if (target.kind === K.ParenthesizedExpression) return this.assignable(target.expression, env)
    if (target.kind === K.PropertyAccessExpression || target.kind === K.ElementAccessExpression) {
      throw new Unsupported("changing an object or array in place is not modeled, because two names can refer to the same object; build a new value instead", target)
    }
    if (target.kind !== K.Identifier) throw new Unsupported("this assignment target is not supported", target)
    const cell = env.cell(target.text)
    if (!cell) throw new Unsupported(`\`${target.text}\` is not a local variable, so assigning to it is not supported`, target)
    if (!cell.mutable) throw new Unsupported(`\`${target.text}\` cannot be reassigned here`, target)
    return cell
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
      case K.NumericLiteral: {
        const value = Number(node.text)
        if (!Number.isSafeInteger(value)) throw new Unsupported("only whole numbers up to 2^53 - 1 are modeled; fractions and larger numbers are not", node)
        return scalar(ir.lit(BigInt(value)), true)
      }
      case K.Identifier: return env.get(node.text) ?? this.global(node)
      case K.ArrowFunction:
      case K.FunctionExpression:
        return { k: "closure", node, env }
      case K.PrefixUnaryExpression: {
        if (node.operator === K.ExclamationToken) return scalar(ir.not(this.bool(node.operand, env)))
        if (node.operator === K.MinusToken) {
          const operand = this.evalExpr(node.operand, env)
          return scalar(ir.neg(this.scalarOf(operand, node.operand, "int")), isNumber(operand))
        }
        throw new Unsupported("this operator is not supported", node)
      }
      case K.ConditionalExpression:
        return this.branch(this.bool(node.condition, env), () => this.evalExpr(node.whenTrue, env), () => this.evalExpr(node.whenFalse, env))
      case K.BinaryExpression: return this.binary(node, env)
      case K.TemplateExpression: {
        let result = ir.lit(this.wellFormed(node.head.text, node))
        for (const span of node.templateSpans as N[]) {
          const part = this.evalExpr(span.expression, env)
          if (part.k !== "scalar" || part.e.ty === "bool") throw new Unsupported(`only strings and bigints can be interpolated, but this is ${describe(part)}`, span.expression)
          const text = part.e.ty === "int" ? ir.toStr(part.e) : part.e
          result = ir.concat(ir.concat(result, text), ir.lit(this.wellFormed(span.literal.text, span)))
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
          if (name === "length" && object.k === "array") return scalar(ir.lit(BigInt(object.items.length)), true)
          if (name === "length" && object.k === "scalar" && object.e.ty === "str") {
            // JavaScript counts UTF-16 units and Lean counts characters, so only a known string has a length here.
            if (object.e.t !== "lit") throw new Unsupported("the length of a string that is not known here is not modeled", node)
            return scalar(ir.lit(BigInt((object.e.value as string).length)), true)
          }
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
      if (leftValue.e.ty !== rightValue.e.ty || !!leftValue.num !== !!rightValue.num) throw new Unsupported(`cannot compare ${describe(leftValue)} with ${describe(rightValue)}`, node)
      const equal = ir.eq(leftValue.e, rightValue.e)
      return scalar(operator === K.EqualsEqualsEqualsToken ? equal : ir.not(equal))
    }
    if (operator === K.EqualsEqualsToken || operator === K.ExclamationEqualsToken) throw new Unsupported("use === and !==; loose equality is not modeled", node)
    if (operator >= K.FirstAssignment && operator <= K.LastAssignment) throw new Unsupported("an assignment used as a value is not supported; write it as its own statement", node)
    return this.arithmetic(operator, leftValue, rightValue, node)
  }

  /** `+ - * / %` and the comparisons, on values already evaluated. */
  private arithmetic(operator: number, leftValue: Value, rightValue: Value, node: N): Value {
    if (operator === K.PlusToken && leftValue.k === "scalar" && rightValue.k === "scalar" && leftValue.e.ty === "str" && rightValue.e.ty === "str") {
      return scalar(ir.concat(leftValue.e, rightValue.e))
    }
    const left = this.scalarOf(leftValue, node.left ?? node, "int")
    const right = this.scalarOf(rightValue, node.right ?? node, "int")
    if (isNumber(leftValue) !== isNumber(rightValue)) throw new Unsupported(`cannot combine ${describe(leftValue)} with ${describe(rightValue)}`, node)
    if (isNumber(leftValue)) {
      // A `number` is modeled as the whole number it holds. That is exact for
      // these operators as long as the result stays within what a double
      // holds exactly, which each use must prove.
      const exact = (result: Expr) => {
        this.emit("overflow", ir.isSafe(result), node)
        return scalar(result, true)
      }
      switch (operator) {
        case K.PlusToken: return exact(ir.add(left, right))
        case K.MinusToken: return exact(ir.sub(left, right))
        case K.AsteriskToken: return exact(ir.mul(left, right))
        case K.PercentToken:
          this.emit("nan", ir.not(ir.eq(right, ir.lit(0n))), node)
          return scalar(ir.mod(left, right), true)
        case K.SlashToken:
          throw new Unsupported("dividing numbers can give a fraction, which is not modeled; write Math.floor(a / b) or Math.trunc(a / b), or use bigint", node)
      }
    }
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
        const position = this.evalExpr(index, env)
        if (!isNumber(position) || position.k !== "scalar" || position.e.t !== "lit") throw new Unsupported("an array can only be indexed by a position that is known here", node)
        const item = object.items[Number(position.e.value)]
        if (!item) throw new Unsupported("this index is outside the array", node)
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
    if (callee.kind === K.Identifier && !env.get(callee.text) && node.arguments.length === 1 && this.isBuiltin(callee)) {
      if (callee.text === "String") return this.text(args()[0]!, node)
      if (callee.text === "BigInt" || callee.text === "Number") {
        const [value] = args()
        const integer = this.scalarOf(value!, node, "int")
        // Every whole number is a bigint, but only some bigints fit a number exactly.
        if (callee.text === "Number" && !isNumber(value!)) this.emit("overflow", ir.isSafe(integer), node)
        return scalar(integer, callee.text === "Number")
      }
    }
    if (callee.kind === K.PropertyAccessExpression && callee.expression.kind === K.Identifier && callee.expression.text === "Math" &&
      !env.get("Math") && this.isBuiltin(callee.expression)) return this.math(callee.name.text, node, env)
    if (callee.kind === K.PropertyAccessExpression && !this.isNamespace(callee.expression, env)) {
      const method = callee.name.text as string
      return this.over(this.evalExpr(callee.expression, env), receiver => {
        if (receiver.k === "bottom") return BOTTOM
        if (receiver.k === "scalar" && method === "toString" && node.arguments.length === 0) return this.text(receiver, node)
        if (receiver.k === "array") return this.arrayMethod(receiver.items, method, args(), node)
        if (receiver.k === "record" && receiver.fields.has(method)) return this.call(receiver.fields.get(method)!, args(), node)
        throw new Unsupported(`calling \`.${method}\` on ${describe(receiver)} is not supported`, node)
      })
    }
    return this.call(this.evalExpr(callee, env), args(), node)
  }

  /** The `Math` functions that keep whole numbers whole. */
  private math(name: string, node: N, env: Env): Value {
    const parameters = node.arguments as N[]
    const number = (argument: N) => {
      const value = this.evalExpr(argument, env)
      if (!isNumber(value)) throw new Unsupported(`Math.${name} is modeled for numbers, but this is ${describe(value)}`, argument)
      return (value as { e: Expr }).e
    }
    const [first] = parameters
    if (first && parameters.length === 1 && (name === "floor" || name === "trunc" || name === "ceil" || name === "round")) {
      let inner = first
      while (inner.kind === K.ParenthesizedExpression) inner = inner.expression
      if (inner.kind !== K.BinaryExpression || inner.operatorToken.kind !== K.SlashToken) return scalar(number(first), true)
      // Rounding a quotient of whole numbers. Dividing two exactly held whole
      // numbers and rounding gives the same integer as exact division; that
      // does not hold for Math.round, whose halfway cases depend on the fraction.
      if (name === "round") throw new Unsupported("Math.round of a quotient is not modeled; use Math.floor or Math.trunc", node)
      const a = number(inner.left)
      const b = number(inner.right)
      this.emit("nan", ir.not(ir.eq(b, ir.lit(0n))), inner)
      const truncated = ir.div(a, b)
      if (name === "trunc") return scalar(truncated, true)
      const inexact = ir.not(ir.eq(ir.mod(a, b), ir.lit(0n)))
      const negative = ir.not(ir.eq(ir.lt(a, ir.lit(0n)), ir.lt(b, ir.lit(0n))))
      return scalar(name === "floor"
        ? ir.ite(ir.and(inexact, negative), ir.sub(truncated, ir.lit(1n)), truncated)
        : ir.ite(ir.and(inexact, ir.not(negative)), ir.add(truncated, ir.lit(1n)), truncated), true)
    }
    if (first && parameters.length === 1 && name === "abs") {
      const value = number(first)
      return scalar(ir.ite(ir.lt(value, ir.lit(0n)), ir.neg(value), value), true)
    }
    if (first && parameters.length === 1 && name === "sign") {
      const value = number(first)
      return scalar(ir.ite(ir.lt(value, ir.lit(0n)), ir.lit(-1n), ir.ite(ir.eq(value, ir.lit(0n)), ir.lit(0n), ir.lit(1n))), true)
    }
    if (parameters.length >= 1 && (name === "min" || name === "max") && parameters.every(p => p.kind !== K.SpreadElement)) {
      return scalar(parameters.map(number).reduce((best, value) => ir.ite(name === "min" ? ir.lt(value, best) : ir.lt(best, value), value, best)), true)
    }
    throw new Unsupported(`Math.${name} is not supported`, node)
  }

  /** `String(x)` and `x.toString()` for the scalars whose text Lean and JavaScript agree on. */
  private text(value: Value, at: N): Value {
    if (value.k === "scalar" && value.e.ty === "str") return value
    if (value.k === "scalar" && value.e.ty === "int") return scalar(ir.toStr(value.e))
    throw new Unsupported(`converting ${describe(value)} to a string is not supported`, at)
  }

  /** Whether an identifier refers to a global from TypeScript's own library files. */
  private isBuiltin(node: N): boolean {
    const declaration = this.checker.getSymbolAtLocation(node)?.declarations[0]?.resolve()
    return !!declaration && this.program.isSourceFileDefaultLibrary(declaration.getSourceFile())
  }

  private arrayMethod(items: Value[], method: string, args: Value[], node: N): Value {
    const [first, second] = args
    const expected = method === "reduce" ? 2 : 1
    if (!first || args.length !== expected) {
      throw new Unsupported(method === "reduce" ? "`.reduce` is supported with a callback and an initial value" : `\`.${method}\` is supported with exactly one argument`, node)
    }
    // Callbacks also receive an index, which is a number and so not modeled.
    if (method !== "includes" && first.k === "closure" && first.node.parameters.length > expected) {
      throw new Unsupported("the index parameter of an array callback is not supported", node)
    }
    switch (method) {
      case "reduce":
        return items.reduce((accumulator, item) => this.call(first, [accumulator, item], node), second!)
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
        if (ARRAY_MUTATORS.has(method)) {
          throw new Unsupported("changing an object or array in place is not modeled, because two names can refer to the same object; build a new value instead", node)
        }
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

/** Whether a statement can leave its enclosing block early: by returning, throwing, breaking or continuing. */
function canExit(node: N | undefined): boolean {
  if (!node) return false
  if (node.kind === K.ReturnStatement || node.kind === K.ThrowStatement || node.kind === K.BreakStatement || node.kind === K.ContinueStatement) return true
  if (node.kind === K.ArrowFunction || node.kind === K.FunctionExpression || node.kind === K.FunctionDeclaration) return false
  return node.forEachChild((child: N) => canExit(child) || undefined) === true
}

/** The plain names an assignment target writes to. Property and element targets write to no name. */
function collectNames(target: N, into: Set<string>) {
  if (target.kind === K.Identifier) into.add(target.text)
  else if (target.kind === K.ParenthesizedExpression) collectNames(target.expression, into)
}
