// Translate law files into proof obligations by evaluating the TypeScript
// symbolically. Functions are inlined at their call sites, records and arrays
// are resolved here, and anything outside the supported subset is refused at
// the exact node instead of being approximated.

import { ElementFlags, NodeFlags, SignatureKind, SymbolFlags, SyntaxKind as K, TypeFlags, type Checker, type Node, type Program, type SourceFile, type Type } from "./compiler.ts"
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

/**
 * Raised where the translation needs a plain value, such as the number of
 * times a loop runs, and has an expression in the inputs instead. If one of
 * those inputs has few values, the law is translated once per value.
 */
class NeedsValue extends Error {
  readonly inputs: Set<string>
  readonly refusal: Unsupported
  constructor(inputs: Set<string>, refusal: Unsupported) {
    super(refusal.message)
    this.inputs = inputs
    this.refusal = refusal
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
  /** Inputs this instance fixes to one value, because the translation had to know it. */
  fixed: Map<string, Expr>
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
  /** Constants met while translating, so inputs can be aimed at them even when translation stops early. */
  mentioned: Expr[]
  /** Every `expect()` in the law and in the functions it calls, keyed by `file:line:column`. */
  expectSites: Map<string, { file: string; line: number; column: number; text: string }>
  /** Set when the law could not be translated. */
  problem: ({ kind: "unsupported" | "invalid"; message: string } & Location) | undefined
}

type Value =
  /** `num` marks an integer expression that stands for a `number` rather than a bigint. */
  | { k: "scalar"; e: Expr; num?: boolean }
  | { k: "record"; fields: Map<string, Value>; own?: Ownership }
  | { k: "array"; items: Value[]; own?: Ownership }
  | { k: "closure"; node: N; env: Env }
  | { k: "choice"; cond: Expr; a: Value; b: Value }
  /** The result of a path that throws. It never reaches a caller, so it merges away. */
  | { k: "bottom" }
  /** `undefined`, as returned by a function that returns nothing. */
  | { k: "void" }
  /** A `const` or `let` whose block has been entered but whose declaration has not run yet. */
  | { k: "uninitialized" }

/** An object or an array: a value that code can change in place. */
type Stored = Extract<Value, { k: "record" | "array" }>

/**
 * What lets an object be changed in place. Values here are shared exactly
 * where JavaScript shares them: two names for one object hold one `Stored`,
 * so a change through either is seen through both. That only holds for an
 * object the code being translated created itself, in the run of code that
 * is still going on (`epoch`), and that has not been copied into a merge of
 * two objects since. Everything else has no `own` and cannot be changed: the
 * law's inputs, module constants, values a `describe` shares between laws.
 */
interface Ownership {
  /** The run of code that created the object: one translation of a law, or one module constant's initializer. */
  epoch: number
  /** Creation order, to tell objects that existed at a saved moment from ones created after it. */
  born: number
}

/** One change to an object, kept so that it can be undone. `previous` is undefined where an array had no such position. */
interface Write {
  target: Stored
  slot: string | number
  previous: Value | undefined
}

/** For each object changed since some moment, the values its changed slots ended up with. */
type Changes = Map<Stored, Map<string | number, Value | undefined>>

let epochs = 0
let objectsCreated = 0

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

/**
 * Every binding made in a scope is logged, so that evaluating one branch of a
 * condition can be undone before evaluating the other. Only scopes that
 * existed before the branch are rolled back; scopes created inside it belong
 * to whatever the branch produced, such as a closure it returned.
 */
let scopesCreated = 0
const bindingLog: { env: Env; name: string; previous: Cell | undefined }[] = []

class Env {
  readonly serial = scopesCreated++
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
    bindingLog.push({ env: this, name, previous: this.vars.get(name) })
    this.vars.set(name, cell)
    return cell
  }
  /** Put a binding back to what it was, or remove it. */
  revert(name: string, previous: Cell | undefined) {
    if (previous) this.vars.set(name, previous)
    else this.vars.delete(name)
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

/** The state at one moment: values of the live reassignable variables, how far the logs had got, and what existed. */
interface Saved {
  values: Value[]
  logged: number
  scopes: number
  written: number
  objects: number
}

/** Where control goes when a statement list ends, breaks out of, or continues a loop. */
interface Flow {
  next: () => Value
  brk?: () => Value
  cont?: () => Value
}

const BOTTOM: Value = { k: "bottom" }
const VOID: Value = { k: "void" }
const UNINITIALIZED: Value = { k: "uninitialized" }
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
const MAX_INSTANCES = 256
const NUMBER_HELP = "`number` covers fractions, NaN and infinities, which are not modeled; use `Integer` from pudding for whole numbers, or bigint"
const MAX_ALTERNATIVES = 64
const MODULE_DECLARATIONS = new Set<number>([
  K.ImportDeclaration, K.ExportDeclaration, K.ExportAssignment, K.VariableStatement, K.FunctionDeclaration, K.ClassDeclaration,
  K.InterfaceDeclaration, K.TypeAliasDeclaration, K.EnumDeclaration, K.ModuleDeclaration, K.ImportEqualsDeclaration, K.EmptyStatement,
])
const DECLARATIONS_WITHOUT_VALUE = new Set<number>([K.ImportDeclaration, K.InterfaceDeclaration, K.TypeAliasDeclaration, K.EmptyStatement])
/** Array methods that change nothing and return no reference into the array, given elements that are plain values. */
const READING_METHODS = new Set([
  "includes", "some", "every", "map", "reduce", "reduceRight", "filter", "find", "findIndex", "findLast", "findLastIndex", "indexOf", "lastIndexOf",
  "join", "slice", "concat", "at", "flat", "flatMap", "keys", "values", "entries", "toString",
])
/** Functions that write to the object they are given first. */
const WRITERS = /^(Object\.(assign|defineProperty|defineProperties|setPrototypeOf)|Reflect\.(set|defineProperty|setPrototypeOf|deleteProperty))$/
/** Built-in functions that only read what they are given. The last group returns what is inside it. */
const READERS = /^(Object\.(keys|isFrozen|hasOwn|getOwnPropertyNames)|Array\.isArray|JSON\.stringify|String|Boolean)$/
const SHALLOW_READERS = /^(Object\.(values|entries|freeze|fromEntries)|Array\.from|structuredClone)$/
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
    case "uninitialized": return "a variable that is not initialized yet"
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
  /** How many merges of variable state are in progress in the function being evaluated. */
  private merging = 0
  /** Module constants whose initializers are being evaluated, innermost last. */
  private loading: { file: string; position: number }[] = []
  private mentioned: Expr[] = []
  private sites: Law["expectSites"] | undefined
  private scanned = new Set<Node>()
  private readonly importing = new Map<string, boolean>()
  private readonly exportsUsed = new Map<Node, string>()
  /** Set when some file of the program replaces part of a built-in, which the models of built-ins cannot see. */
  private tampering: { message: string; node: Node } | undefined | null = null
  /** The run of code whose objects may be changed in place right now. */
  private epoch = 0
  /** Every change made to an object in place since the current law instance started, oldest first. */
  private writes: Write[] = []
  private readonly facts = new Map<Node, { assigned: Set<string>; mentioned: Set<string>; returnsValue: boolean; usesVar: Node | undefined }>()
  private instance: LawInstance | undefined

  constructor(program: Program, checker: Checker, moduleName: string) {
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
    const name = this.libraryExport(callee)
    return name === "law" || name === "describe" ? { kind: name, modifier } : undefined
  }

  /**
   * The export of this library that an identifier refers to, if any. Decided
   * by following the name to its import, because a local declaration can
   * reuse any of these names and the code being read may be in any module.
   */
  private libraryExport(identifier: N): string | undefined {
    let known = this.exportsUsed.get(identifier)
    if (known === undefined) {
      const declaration = this.checker.getSymbolAtLocation(identifier)?.declarations[0]?.resolve() as N
      known = declaration?.kind === K.ImportSpecifier && declaration.parent.parent.parent.moduleSpecifier.text === this.moduleName
        ? ((declaration.propertyName ?? declaration.name).text as string) : ""
      this.exportsUsed.set(identifier, known)
    }
    return known || undefined
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
    if (env) this.enter(statements, env)
    const invalid = (statement: N, message: string) => laws.push({
      name: sourceText(statement), ...locate(statement), index: -1, mode: "run", proof: undefined, instances: [], mentioned: [], expectSites: new Map(),
      problem: { kind: "invalid", message, ...locate(statement) },
    })
    for (const statement of statements) {
      if (statement.kind !== K.ExpressionStatement) {
        // Anything else at the top of a law file could register laws that are never read, such as `if (x) law(...)`.
        if (!env && !MODULE_DECLARATIONS.has(statement.kind)) invalid(statement, "only law() and describe() calls and declarations are allowed in a law file")
        if (!env || DECLARATIONS_WITHOUT_VALUE.has(statement.kind)) continue
        try {
          // What a describe declares is shared by its laws, so no law may change it: its epoch ends here.
          this.writes = []
          this.epoch = ++epochs
          if (statement.kind === K.VariableStatement) this.declare(statement, env)
          else if (statement.kind !== K.FunctionDeclaration) invalid(statement, "only laws and declarations are allowed inside describe()")
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
          name, ...locate(call), index, mode: modifier === "todo" ? "todo" : "skip", proof: undefined, instances: [], mentioned: [], expectSites: new Map(), problem: undefined,
          // A law marked `only` narrows its file even when a name filter leaves it out.
          ...(own === "only" && modifier !== "todo" ? { only: true } : {}),
        })
        continue
      }
      const law: Law & { only?: boolean } = this.translateLaw(call, index, name, env)
      if (own === "only") law.only = true
      laws.push(law)
    }
  }

  private isCallTo(node: N, name: string): boolean {
    return node?.kind === K.CallExpression && node.expression.kind === K.Identifier && this.libraryExport(node.expression) === name
  }

  private translateLaw(call: N, index: number, name: string, scope: Env | undefined): Law {
    const args = call.arguments as N[]
    const law: Law = {
      name, ...locate(call), index, mode: "run", proof: undefined, instances: [], mentioned: [], expectSites: new Map(), problem: undefined,
    }
    const invalid = (message: string, node: Node) => {
      law.problem = { kind: "invalid", message, ...locate(node) }
      return law
    }
    const hasDomain = this.isCallTo(args[1], "domain")
    const callback = args[hasDomain ? 2 : 1]
    const options = args[hasDomain ? 3 : 2]
    if (callback?.kind !== K.ArrowFunction && callback?.kind !== K.FunctionExpression) return invalid("law() needs a callback", call)
    if (callback.parameters.length !== (hasDomain ? 1 : 0)) return invalid(hasDomain ? "the callback takes exactly one parameter" : "a law without a domain takes no parameter", callback)
    if (callback.asteriskToken || callback.modifiers?.some((m: N) => m.kind === K.AsyncKeyword)) return invalid("a law callback must be an ordinary synchronous function", callback)
    const [parameter] = callback.parameters as N[]
    if (parameter && (parameter.dotDotDotToken || parameter.initializer || parameter.questionToken)) return invalid("the callback's parameter must be plain: no rest, default or optional marker", parameter)
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
    this.mentioned = law.mentioned
    this.sites = law.expectSites
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
        const instance: LawInstance = { assumptions: [], fixed: new Map(), binders: [], arg: undefined, obligations: [] }
        this.instance = instance
        if (hasDomain) instance.arg = this.instantiate(alternative, instance)
        law.instances.push(instance)
      }
      const waiting = law.instances
      law.instances = []
      while (waiting.length) {
        const instance = waiting.shift()!
        this.instance = instance
        this.pc = [...instance.assumptions]
        this.stack = []
        this.cells = []
        bindingLog.length = 0
        this.writes = []
        this.epoch = ++epochs
        this.steps = 0
        const facts = this.factsOf(callback)
        if (facts.usesVar) throw new Unsupported("`var` is not supported; use `const` or `let`", facts.usesVar)
        this.assigned = [facts.assigned]
        const env = scope ? scope.child() : new Env()
        try {
          if (instance.arg) this.bind(callback.parameters[0].name, this.valueOf(instance.arg), env, true, true)
          const body = callback.body
          if (body.kind === K.Block) this.block(body.statements, env, { next: () => VOID })
          else this.effect(body, env)
          law.instances.push(instance)
        } catch (error) {
          // Split on an input that has few values, and translate each case on its own.
          const input = error instanceof NeedsValue ? instance.binders.find(b => error.inputs.has(b.name) && b.domain && b.domain.length > 1) : undefined
          if (!input || law.instances.length + waiting.length + input.domain!.length > MAX_INSTANCES) {
            // The law is refused as a whole. Keep every instance, so it can still be executed.
            law.instances.push(instance, ...waiting)
            throw error instanceof NeedsValue ? error.refusal : error
          }
          waiting.unshift(...input.domain!.map(value => ({
            ...instance,
            obligations: [],
            binders: instance.binders.map(b => (b === input ? { ...b, domain: [value] } : { ...b })),
            fixed: new Map(instance.fixed).set(input.name, ir.lit(value)),
          })))
        }
      }
      // Whatever a law uses, its model assumes the language's own behaviour.
      // Checked last, so that a law refused for this still has named inputs to be executed with.
      this.assertBuiltinsIntact(call)
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
      this.sites = undefined
      this.scanned = new Set()
    }
    return law
  }

  /**
   * Record the expectations a called function contains, so one that is never
   * reached is noticed like one written in the law itself. Only files that
   * import this library can contain any.
   */
  private noteExpectations(fn: N) {
    if (!this.sites || this.scanned.has(fn)) return
    this.scanned.add(fn)
    const file = fn.getSourceFile() as SourceFile
    let uses = this.importing.get(file.fileName)
    if (uses === undefined) {
      uses = (file.statements as readonly N[]).some(s => s.kind === K.ImportDeclaration && s.moduleSpecifier.text === this.moduleName)
      this.importing.set(file.fileName, uses)
    }
    if (!uses || !fn.body) return
    const visit = (n: N) => {
      if (this.isExpect(n)) {
        let statement = n
        while (statement.parent && statement.kind !== K.ExpressionStatement && statement !== fn.body) statement = statement.parent
        const at = locate(statement)
        this.sites!.set(`${at.file}:${at.line}:${at.column}`, { file: at.file, line: at.line, column: at.column, text: sourceText(statement) })
      }
      n.forEachChild(visit)
    }
    visit(fn.body)
  }

  private collectExpectSites(node: N, law: Law) {
    const visit = (n: N) => {
      if (this.isExpect(n)) {
        let statement = n
        while (statement.parent && statement.kind !== K.ExpressionStatement && statement !== node) statement = statement.parent
        const at = locate(statement)
        law.expectSites.set(`${at.file}:${at.line}:${at.column}`, { file: at.file, line: at.line, column: at.column, text: sourceText(statement) })
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
      if (this.checker.getIndexInfosOfType(type).length) {
        throw new Unsupported(`${name()} allows any number of properties, so its values cannot be listed; use an object type with named properties`, at)
      }
      const fields: [string, Shape][] = []
      for (const property of this.checker.getPropertiesOfType(type)) {
        if (property.flags & SymbolFlags.Optional) throw new Unsupported(`optional property \`${property.name}\` is not supported in an input`, at)
        // A property keyed by a symbol has no string name; its compiler name starts like this.
        if (String(property.escapedName).startsWith("__@")) throw new Unsupported(`${name()} has a property keyed by a symbol, which is not supported in an input`, at)
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
  /**
   * Whether a call is to the `expect` this library exports, and not to
   * something else that happens to have its name. Decided by where the name
   * was imported from, since the code being read may be in any module.
   */
  private isExpect(node: N): boolean {
    return this.isCallTo(node, "expect")
  }

  private startsWithExpect(node: N): boolean {
    let current = node
    while (current) {
      if (this.isExpect(current)) return true
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
    if (!this.isExpect(target) || target.arguments.length !== 1) throw fail()
    const actual = this.evalExpr(target.arguments[0], env)
    const expected = this.evalExpr(node.arguments[0], env)
    const equal = this.equal(actual, expected, node, matcher === "toBe")
    const sides = actual.k === "scalar" && expected.k === "scalar" ? { actual: actual.e, expected: expected.e, negated, num: !!actual.num } : undefined
    this.emit("expect", negated ? ir.not(equal) : equal, node, sides)
  }

  /** Whether two values are equal as `toEqual` sees it, or as `toBe` does when `identity` is set. */
  private equal(a: Value, b: Value, at: Node, identity = false): Expr {
    if (a.k === "bottom" || b.k === "bottom") return ir.FALSE
    if (a.k === "choice") return ir.ite(a.cond, this.equal(a.a, b, at, identity), this.equal(a.b, b, at, identity))
    if (b.k === "choice") return ir.ite(b.cond, this.equal(a, b.a, at, identity), this.equal(a, b.b, at, identity))
    if (this.isPlain(a) && this.isPlain(b)) return this.strictEqual(a, b, at)
    if (identity) throw new Unsupported("toBe compares identity, which is only modeled for booleans, bigints, numbers and strings; use toEqual", at)
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

  /**
   * The value of an expression where the translation cannot go on without
   * one. Inputs this instance has fixed are filled in; if that is not enough,
   * the caller's refusal is raised in a form that lets the law be split.
   */
  private settle(e: Expr, refusal: () => Unsupported): Extract<Expr, { t: "lit" }> {
    const settled = this.instance?.fixed.size ? ir.substitute(e, this.instance.fixed) : e
    if (settled.t === "lit") return settled
    throw new NeedsValue(ir.freeVariables(settled), refusal())
  }

  private under<T>(cond: Expr, run: () => T): T {
    this.pc.push(cond)
    try {
      return run()
    } finally {
      this.pc.pop()
    }
  }

  private save(): Saved {
    return { values: this.cells.map(cell => cell.value), logged: bindingLog.length, scopes: scopesCreated, written: this.writes.length, objects: objectsCreated }
  }

  /** Mark an object as created here and now, which is what allows changing it in place. */
  private fresh<T extends Stored>(value: T): T {
    value.own = { epoch: this.epoch, born: objectsCreated++ }
    return value
  }

  /** Take away the right to change objects in place. Epochs start at 1, so 0 is never the current one. */
  private freeze(...values: Stored[]) {
    for (const value of values) if (value.own) value.own.epoch = 0
  }

  private slot(target: Stored, slot: string | number): Value | undefined {
    return target.k === "record" ? target.fields.get(slot as string) : target.items[slot as number]
  }

  private put(target: Stored, slot: string | number, value: Value | undefined) {
    if (target.k === "record") target.fields.set(slot as string, value!)
    else if (value === undefined) target.items.length = slot as number
    else target.items[slot as number] = value
  }

  /** Change an object in place, remembering what was there. */
  private write(target: Stored, slot: string | number, value: Value) {
    this.writes.push({ target, slot, previous: this.slot(target, slot) })
    this.put(target, slot, value)
  }

  /**
   * Check that an object may be changed in place and that storing `value` in
   * it would not make it contain itself, which nothing here could walk.
   */
  private assertChangeable(target: Stored, value: Value, at: N) {
    if (target.own?.epoch !== this.epoch) {
      throw new Unsupported("changing this object in place is not modeled: it is one of the law's inputs, a shared constant, or the result of a condition choosing between two objects. Copy it first, as in `{ ...value }` or `[...value]`", at)
    }
    const seen = new Set<Value>()
    const inside = (part: Value): boolean => {
      if (part === target) return true
      if (seen.has(part)) return false
      seen.add(part)
      return part.k === "record" ? [...part.fields.values()].some(inside) : part.k === "array" ? part.items.some(inside)
        : part.k === "choice" ? inside(part.a) || inside(part.b) : false
    }
    if (inside(value)) throw new Unsupported("storing an object inside itself is not supported", at)
  }

  /** What each object that existed at `since` holds now in the slots changed after it. */
  private changesSince(since: Saved): Changes | undefined {
    if (this.writes.length === since.written) return undefined
    const changes: Changes = new Map()
    for (let i = since.written; i < this.writes.length; i++) {
      const { target, slot } = this.writes[i]!
      if (target.own!.born >= since.objects) continue
      let slots = changes.get(target)
      if (!slots) changes.set(target, slots = new Map())
      slots.set(slot, this.slot(target, slot))
    }
    return changes.size ? changes : undefined
  }

  /**
   * After the two sides of a condition have each been run and undone, give
   * every object they changed the value of whichever side is taken. `dead`
   * names a side that never continues, so only the other side's changes count.
   */
  private mergeChanges(cond: Expr, whenTrue: Changes | undefined, whenFalse: Changes | undefined, dead?: "true" | "false") {
    if (!whenTrue && !whenFalse) return
    for (const target of new Set([...(whenTrue?.keys() ?? []), ...(whenFalse?.keys() ?? [])])) {
      const a = whenTrue?.get(target)
      const b = whenFalse?.get(target)
      // An array grows one position at a time, so its positions are settled in order.
      const slots = [...new Set([...(a?.keys() ?? []), ...(b?.keys() ?? [])])]
      if (target.k === "array") slots.sort((x, y) => (x as number) - (y as number))
      for (const slot of slots) {
        const now = this.slot(target, slot)
        let onTrue = a?.has(slot) ? a.get(slot) : now
        let onFalse = b?.has(slot) ? b.get(slot) : now
        if (dead === "true") onTrue = onFalse
        if (dead === "false") onFalse = onTrue
        if (onTrue === undefined && onFalse === undefined) continue
        if (onTrue === undefined || onFalse === undefined) throw new Unsupported("an array that grows on only one side of a condition is not supported", undefined)
        const merged = this.merge(cond, onTrue, onFalse)
        if (merged !== now) this.write(target, slot, merged)
      }
    }
  }

  /**
   * Run code that JavaScript may skip or stop part-way, where the model runs
   * all of it. That is the same thing only if the code changes no object that
   * existed before it, so anything else is refused.
   */
  private unchanging<T>(what: string, at: N, run: () => T): T {
    const written = this.writes.length
    const objects = objectsCreated
    const result = run()
    for (let i = written; i < this.writes.length; i++) {
      if (this.writes[i]!.target.own!.born < objects) throw new Unsupported(`${what} changes an object in place, which is not modeled there; make the change in a statement of its own`, at)
    }
    return result
  }

  /** Put variables and bindings back to a saved state, forgetting any declared since. */
  private restore(saved: Saved) {
    this.cells.length = saved.values.length
    this.cells.forEach((cell, i) => (cell.value = saved.values[i]!))
    while (bindingLog.length > saved.logged) {
      const entry = bindingLog.pop()!
      if (entry.env.serial < saved.scopes) entry.env.revert(entry.name, entry.previous)
    }
    // An object created since then is left as it is: only what was produced after the save can still refer to it.
    while (this.writes.length > saved.written) {
      const { target, slot, previous } = this.writes.pop()!
      if (target.own!.born < saved.objects) this.put(target, slot, previous)
    }
  }

  /**
   * Evaluate both sides of a condition and merge their results. Each side
   * starts from the same state. The variables afterwards are as they were
   * before: an expression cannot assign, and a statement branch evaluated
   * this way has already run to the end of its function on both sides.
   * Objects are different, because a change to one outlives the function
   * that made it: each object changed on either side ends up holding the
   * value of the side taken.
   */
  private branch(cond: Expr, whenTrue: () => Value, whenFalse: () => Value, control = false): Value {
    if (cond.t === "lit") return cond.value ? whenTrue() : whenFalse()
    // A branch over statements only keeps their effects if both sides run on to
    // the end of the function. Inside a merge they do not, so reaching here
    // would silently drop assignments. Every such construct is meant to merge
    // instead; this is the net under that.
    if (control && this.merging > 0) throw new Unsupported("this combination of branches and assignments is not supported", undefined)
    const before = this.save()
    const a = this.under(cond, whenTrue)
    const changedA = this.changesSince(before)
    this.restore(before)
    const b = this.under(ir.not(cond), whenFalse)
    const changedB = this.changesSince(before)
    this.restore(before)
    this.mergeChanges(cond, changedA, changedB, a.k === "bottom" ? "true" : b.k === "bottom" ? "false" : undefined)
    return this.merge(cond, a, b)
  }

  /**
   * Run two branches that both continue past the condition, then make every
   * variable hold the value of whichever branch was taken. The code after
   * the condition is then evaluated once, not once per branch.
   */
  private mergeStates(cond: Expr, whenTrue: () => void, whenFalse: () => void) {
    const before = this.save()
    const kept = before.values.length
    this.merging++
    let afterTrue: Value[]
    let afterFalse: Value[]
    let changedTrue: Changes | undefined
    let changedFalse: Changes | undefined
    try {
      this.under(cond, whenTrue)
      afterTrue = this.cells.slice(0, kept).map(cell => cell.value)
      changedTrue = this.changesSince(before)
      this.restore(before)
      this.under(ir.not(cond), whenFalse)
      afterFalse = this.cells.slice(0, kept).map(cell => cell.value)
      changedFalse = this.changesSince(before)
      this.restore(before)
    } finally {
      this.merging--
    }
    this.mergeChanges(cond, changedTrue, changedFalse)
    this.cells.forEach((cell, i) => {
      const a = afterTrue[i]!
      const b = afterFalse[i]!
      cell.value = a === b ? a : this.merge(cond, a, b)
    })
  }

  private merge(cond: Expr, a: Value, b: Value): Value {
    // One object on both sides stays that object, and stays changeable.
    if (a === b) return a
    if (a.k === "bottom") return b
    if (b.k === "bottom") return a
    if (a.k === "scalar" && b.k === "scalar" && a.e.ty === b.e.ty && !!a.num === !!b.num) return scalar(ir.ite(cond, a.e, b.e), a.num)
    // Two objects merged field by field give a third that is neither of them,
    // holding what they hold now. That stays true only while none of the three
    // changes, so all three lose the right to be changed in place.
    if (a.k === "array" && b.k === "array" && a.items.length === b.items.length) {
      this.freeze(a, b)
      return { k: "array", items: a.items.map((item, i) => this.merge(cond, item, b.items[i]!)) }
    }
    if (a.k === "record" && b.k === "record" && a.fields.size === b.fields.size && [...a.fields.keys()].every(key => b.fields.has(key))) {
      this.freeze(a, b)
      return { k: "record", fields: new Map([...a.fields].map(([key, field]) => [key, this.merge(cond, field, b.fields.get(key)!)])) }
    }
    if (a.k === "closure" && b.k === "closure" && a.node === b.node && a.env === b.env) return a
    if (a.k === "void" && b.k === "void") return a
    return { k: "choice", cond, a, b }
  }

  /** Apply an operation to a value, distributing over conditional values. */
  private over(value: Value, apply: (value: Value) => Value): Value {
    value = this.settled(value)
    if (value.k === "choice") return this.branch(value.cond, () => this.over(value.a, apply), () => this.over(value.b, apply))
    return apply(value)
  }

  // ------------------------------------------------------------- functions

  /** What a function's body does that affects how it is evaluated, computed once per function. */
  private factsOf(fn: N) {
    let facts = this.facts.get(fn)
    if (facts) return facts
    facts = { assigned: new Set<string>(), mentioned: new Set<string>(), returnsValue: false, usesVar: undefined }
    const isFunction = (node: N) => node.kind === K.ArrowFunction || node.kind === K.FunctionExpression || node.kind === K.FunctionDeclaration
    const visit = (node: N, nested: boolean) => {
      if (node.kind === K.Identifier) facts!.mentioned.add(node.text)
      if (node.kind === K.BinaryExpression && node.operatorToken.kind >= K.FirstAssignment && node.operatorToken.kind <= K.LastAssignment) {
        collectNames(node.left, facts!.assigned)
      }
      if ((node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
        (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)) collectNames(node.operand, facts!.assigned)
      if (node.kind === K.ReturnStatement && node.expression && !nested) facts!.returnsValue = true
      // A `var` belongs to the whole function wherever it is written, even in a block that never runs.
      if (node.kind === K.VariableDeclarationList && !(node.flags & (NodeFlags.Let | NodeFlags.Const)) && !nested) facts!.usesVar ??= node
      node.forEachChild((child: N) => visit(child, nested || isFunction(child)))
    }
    for (const parameter of parametersOf(fn)) visit(parameter, false)
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
      // A `let` without an initializer holds undefined until it is assigned.
      this.bind(declaration.name, declaration.initializer ? this.evalExpr(declaration.initializer, env) : VOID, env, false, reassignable)
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
    if (facts.usesVar) throw new Unsupported("`var` is not supported; use `const` or `let`", facts.usesVar)
    this.noteExpectations(node)
    // A function that reads or writes a variable someone reassigns would need
    // that variable's value at the moment of the call, on every path. That is
    // not tracked, so such closures are refused.
    for (const name of fn.env.mutableNames()) {
      if (facts.mentioned.has(name)) throw new Unsupported(`this function uses \`${name}\`, a variable that is reassigned outside it; that is not modeled`, at)
    }
    const env = fn.env.child()
    const live = this.cells.length
    // A call runs to its own end, whatever its caller is in the middle of.
    const merging = this.merging
    this.merging = 0
    this.stack.push(node)
    this.assigned.push(facts.assigned)
    try {
      // A function expression with a name can call itself by it, whatever the name means outside.
      if (node.kind === K.FunctionExpression && node.name) env.set(node.name.text, fn)
      // Every parameter is in scope, uninitialized, while the defaults before it run.
      const parameters = parametersOf(node)
      for (const parameter of parameters) for (const name of boundNames(parameter.name)) env.set(name, UNINITIALIZED)
      parameters.forEach((parameter, i) => {
        if (parameter.dotDotDotToken) throw new Unsupported("rest parameters are not supported", parameter)
        let value = args[i]
        // A default applies when the argument is missing or undefined.
        if (value?.k === "choice" && parameter.initializer) throw new Unsupported("an argument that may or may not be undefined, for a parameter with a default, is not supported", at)
        if (!value || value.k === "void") {
          if (parameter.initializer) value = this.evalExpr(parameter.initializer, env)
          else if (!value) throw new Unsupported("a call must pass every parameter that has no default", at)
        }
        this.bind(parameter.name, value, env, false, true)
      })
      if (node.body.kind !== K.Block) return this.evalExpr(node.body, env)
      // Reaching the end of a function that returns values elsewhere yields
      // undefined where a value is expected. Like a throw, that is allowed
      // only where it is proved unreachable.
      // The body has a scope of its own, so a closure made by a default does not see what the body declares.
      return this.block(node.body.statements, env.child(), {
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
      this.merging = merging
    }
  }

  /**
   * Evaluate a block in its own scope. Entering a block makes its function
   * declarations callable at once, and puts its `const` and `let` names in
   * scope before they hold a value, exactly as JavaScript does; reading one
   * early is an error there and is refused here.
   */
  private block(statements: readonly N[], scope: Env, flow: Flow): Value {
    this.enter(statements, scope)
    return this.exec(statements, 0, scope, flow)
  }

  private enter(statements: readonly N[], scope: Env) {
    for (const statement of statements) {
      if (statement.kind === K.FunctionDeclaration && statement.name) scope.set(statement.name.text, { k: "closure", node: statement, env: scope })
      else if (statement.kind === K.VariableStatement) {
        for (const declaration of statement.declarationList.declarations as N[]) {
          for (const name of boundNames(declaration.name)) scope.set(name, UNINITIALIZED)
        }
      } else if (statement.kind === K.ClassDeclaration && statement.name) scope.set(statement.name.text, UNINITIALIZED)
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
      block ? this.block(block.kind === K.Block ? block.statements : [block], env.child(), to) : to.next()
    switch (statement.kind) {
      case K.EmptyStatement: return rest()
      case K.VariableStatement:
        this.declare(statement, env)
        return rest()
      case K.FunctionDeclaration:
        // Declared when its block was entered.
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
          return this.branch(cond, () => run(statement.thenStatement, after), () => run(statement.elseStatement, after), true)
        }
        const stop: Flow = { next: () => VOID }
        this.mergeStates(cond, () => run(statement.thenStatement, stop), () => run(statement.elseStatement, stop))
        return rest()
      }
      case K.SwitchStatement: {
        const subject = this.evalExpr(statement.expression, env)
        const clauses = statement.caseBlock.clauses as N[]
        // The whole switch is one block: its declarations exist before any label is evaluated.
        const scope = env.child()
        this.enter(clauses.flatMap(clause => clause.statements as N[]), scope)
        // Entering at a clause runs it and every clause below it until a break.
        const statementsFrom = (start: number) => clauses.slice(start).flatMap(clause => clause.statements as N[])
        const matchesAt = (clause: N) => {
          const label = this.evalExpr(clause.expression, scope)
          return this.scalarOf(this.over(subject, value => this.over(label, candidate => scalar(this.strictEqual(value, candidate, clause)))), clause, "bool")
        }
        for (const [index, clause] of clauses.entries()) {
          if (clause.kind === K.DefaultClause && index !== clauses.length - 1) throw new Unsupported("`default` must be the last clause of a switch", clause)
        }
        if (!canExit(statement)) {
          // Nothing leaves the switch early, so each clause is a branch whose assignments are merged.
          const stop: Flow = { next: () => VOID }
          const settle = (index: number): void => {
            const clause = clauses[index]
            if (!clause) return
            if (clause.kind === K.DefaultClause) return void this.exec(statementsFrom(index), 0, scope, stop)
            this.mergeStates(matchesAt(clause), () => void this.exec(statementsFrom(index), 0, scope, stop), () => settle(index + 1))
          }
          settle(0)
          return rest()
        }
        const bodyFrom = (start: number) => this.exec(statementsFrom(start), 0, scope, { ...flow, next: rest, brk: rest })
        const from = (index: number): Value => {
          const clause = clauses[index]
          if (!clause) return rest()
          if (clause.kind === K.DefaultClause) return bodyFrom(index)
          return this.branch(matchesAt(clause), () => bodyFrom(index), () => from(index + 1), true)
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
        const header = env.child()
        for (const name of boundNames(declared[0].name)) header.set(name, UNINITIALIZED)
        const body = statement.statement
        const loop = (items: Value, after: () => Value): Value => {
          if (items.k === "bottom") return BOTTOM
          if (items.k !== "array") throw new Unsupported(`a loop needs an array whose length is known here, but this is ${describe(items)}`, statement.expression)
          const iterate = (index: number): Value => {
            const item = items.items[index]
            if (!item) return after()
            const scope = env.child()
            this.bind(declared[0].name, item, scope, false, reassignable)
            const onward = () => iterate(index + 1)
            return this.block(body.kind === K.Block ? body.statements : [body], scope.child(), { next: onward, cont: onward, brk: after })
          }
          return iterate(0)
        }
        // The list itself may depend on a condition. If the body cannot leave
        // the loop, each possible list is run and the variables are merged;
        // otherwise each runs on to the end of the function.
        const run = (items: Value): Value => {
          items = this.settled(items)
          if (items.k !== "choice") return loop(items, rest)
          const choice = items
          if (canExit(body)) return this.branch(choice.cond, () => run(choice.a), () => run(choice.b), true)
          const each = (list: Value): void => {
            list = this.settled(list)
            if (list.k === "choice") {
              const inner = list
              this.mergeStates(inner.cond, () => each(inner.a), () => each(inner.b))
            } else loop(list, () => VOID)
          }
          each(choice)
          return rest()
        }
        return run(this.evalExpr(statement.expression, header))
      }
      case K.WhileStatement:
      case K.DoStatement:
      case K.ForStatement: {
        // These loops are unrolled by running them: the condition must come
        // out as plainly true or false each time round, as it does when it
        // only depends on a counter and on lengths known here.
        const scope = env.child()
        const initializer = statement.kind === K.ForStatement ? statement.initializer : undefined
        if (initializer?.kind === K.VariableDeclarationList) {
          for (const declaration of initializer.declarations as N[]) for (const name of boundNames(declaration.name)) scope.set(name, UNINITIALIZED)
          this.declare(initializer, scope)
        } else if (initializer) this.effect(initializer, scope)
        const condition = statement.kind === K.ForStatement ? statement.condition : statement.expression
        const body = statement.statement
        let rounds = 0
        const test = (): Value => {
          const cond = condition ? this.bool(condition, scope) : ir.TRUE
          const goes = this.settle(cond, () => new Unsupported("how many times this loop runs depends on a value that is not known here", condition))
          return goes.value ? round() : rest()
        }
        const step = (): Value => {
          if (statement.kind === K.ForStatement && statement.incrementor) this.effect(statement.incrementor, scope)
          return test()
        }
        const round = (): Value => {
          if (++rounds > MAX_ITERATIONS) throw new Unsupported(`this loop runs more than ${MAX_ITERATIONS} times, which is too many to unroll`, statement)
          return this.block(body.kind === K.Block ? body.statements : [body], scope.child(), { next: step, cont: step, brk: rest })
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
      const place = this.place(node.left, env)
      if (place) {
        // JavaScript's order: the object and the key, then the old value, then the right-hand side, then the store.
        const old = base === undefined ? undefined : place.read()
        const right = this.evalExpr(node.right, env)
        place.store(old === undefined ? right : this.arithmetic(base!, old, right, node))
        return
      }
      const cell = this.assignable(node.left, env)
      // The right-hand side is evaluated first; it cannot change the variable, because closures over it are refused.
      const right = this.evalExpr(node.right, env)
      cell.value = base === undefined ? right : this.arithmetic(base, cell.value, right, node)
      return
    }
    if ((node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
      (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)) {
      const place = this.place(node.operand, env)
      if (place) {
        const old = place.read()
        place.store(this.arithmetic(node.operator === K.PlusPlusToken ? K.PlusToken : K.MinusToken, old, scalar(ir.lit(1n), isNumber(old)), node))
        return
      }
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

  /**
   * Where an assignment to a property or to a position of an array lands, or
   * undefined when the target is a plain variable. The object and the key are
   * evaluated here, once. The object may be one of several depending on a
   * condition; then each is read and stored to under its own condition.
   */
  private place(target: N, env: Env): { read: () => Value; store: (value: Value) => void } | undefined {
    while (target.kind === K.ParenthesizedExpression || target.kind === K.NonNullExpression) target = target.expression
    if (target.kind !== K.PropertyAccessExpression && target.kind !== K.ElementAccessExpression) return undefined
    if (target.questionDotToken) throw new Unsupported("optional chaining is not supported", target)
    if (target.kind === K.PropertyAccessExpression && this.isNamespace(target.expression, env)) throw new Unsupported("assigning to something a module exports is not supported", target)
    const holder = this.evalExpr(target.expression, env)
    const key = target.kind === K.PropertyAccessExpression ? undefined : this.evalExpr(target.argumentExpression, env)
    const slotOf = (object: Value): [Stored, string | number] => {
      if (object.k === "array" && key) {
        const refusal = () => new Unsupported("an array can only be assigned to at a position that is known here", target)
        if (!isNumber(key) || key.k !== "scalar") throw refusal()
        const position = this.settle(key.e, refusal).value as bigint
        if (position < 0n || position >= BigInt(object.items.length)) throw new Unsupported("assigning outside the array, which would grow it, is not supported; use `.push`", target)
        return [object, Number(position)]
      }
      if (object.k !== "record") throw new Unsupported(`assigning to a property of ${describe(object)} is not supported`, target)
      const name = key ? this.scalarOf(key, target.argumentExpression, "str") : ir.lit(target.name.text as string)
      if (name.t !== "lit") throw new Error("a key that is not known is settled before this")
      if (name.value === "__proto__") throw new Unsupported("assigning to `__proto__` is not modeled", target)
      if (!object.fields.has(name.value as string)) throw new Unsupported(`assigning to \`${name.value}\` would add a property to the object, which is not modeled; give it the property where it is created`, target)
      return [object, name.value as string]
    }
    // A key that is not known here is compared with every property name, as
    // it is when reading. Matching none would add a property, so that case
    // has to be proved impossible.
    const each = (object: Value, apply: (stored: Stored, slot: string | number) => Value): Value => {
      if (object.k === "bottom") return BOTTOM
      const name = object.k === "record" && key ? this.scalarOf(key, target.argumentExpression, "str") : undefined
      if (object.k !== "record" || !name || name.t === "lit") return apply(...slotOf(object))
      const names = [...object.fields.keys()]
      const pick = (i: number): Value => {
        if (i === names.length) {
          this.emit("missing", ir.FALSE, target)
          return BOTTOM
        }
        return this.branch(ir.eq(name, ir.lit(names[i]!)), () => apply(object, names[i]!), () => pick(i + 1))
      }
      return pick(0)
    }
    return {
      read: () => this.over(holder, object => each(object, (stored, slot) => this.slot(stored, slot)!)),
      store: value => void this.over(holder, object => each(object, (stored, slot) => {
        this.assertChangeable(stored, value, target)
        this.write(stored, slot, value)
        return VOID
      })),
    }
  }

  private assignable(target: N, env: Env): Cell {
    if (target.kind === K.ParenthesizedExpression) return this.assignable(target.expression, env)
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
        return this.note(ir.lit(this.wellFormed(node.text, node)))
      case K.TrueKeyword: return scalar(ir.TRUE)
      case K.FalseKeyword: return scalar(ir.FALSE)
      case K.BigIntLiteral: return this.note(ir.lit(BigInt(node.text.replace(/n$/, "").replaceAll("_", ""))))
      case K.NumericLiteral: {
        const value = Number(node.text)
        if (!Number.isSafeInteger(value)) throw new Unsupported("only whole numbers up to 2^53 - 1 are modeled; fractions and larger numbers are not", node)
        return this.note(ir.lit(BigInt(value)), true)
      }
      case K.Identifier: return this.read(node, env)
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
            fields.set(property.name.text, this.read(property.name, env, true))
          } else if (property.kind === K.PropertyAssignment && (property.name.kind === K.Identifier || property.name.kind === K.StringLiteral)) {
            // In an object literal this name sets the prototype instead of storing a property.
            if (property.name.text === "__proto__") throw new Unsupported("`__proto__` in an object literal sets the prototype, which is not modeled", property)
            fields.set(property.name.text, this.evalExpr(property.initializer, env))
          } else throw new Unsupported("methods, accessors and computed property names are not supported in object literals", property)
        }
        return this.fresh({ k: "record", fields })
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
        return this.fresh({ k: "array", items })
      }
      case K.PropertyAccessExpression: {
        if (node.questionDotToken) throw new Unsupported("optional chaining is not supported", node)
        if (this.isNamespace(node.expression, env)) return this.global(node.name)
        const name = node.name.text as string
        if (name === "__proto__") throw new Unsupported("reading `__proto__` is not modeled", node)
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

  /** A literal from the source, remembered as a value worth trying as an input. */
  private note(literal: Expr, num = false): Value {
    if (this.mentioned.length < 256) this.mentioned.push(literal)
    return scalar(literal, num)
  }

  /** The value a name stands for: a local binding, or else a module-level declaration. */
  private read(node: N, env: Env, shorthand = false): Value {
    const local = env.get(node.text)
    if (local?.k === "uninitialized") throw new Unsupported(`\`${node.text}\` is read before its declaration has run, which throws`, node)
    if (local) return this.settled(local)
    if (node.text === "undefined") {
      const symbol = shorthand ? undefined : this.checker.getSymbolAtLocation(node)
      if (symbol && this.checker.isUndefinedSymbol(symbol)) return VOID
    }
    return this.global(node, shorthand)
  }

  /**
   * A value that depends on a condition, reduced by what is already known on
   * this path. After `if (x !== undefined)`, a variable that holds something
   * or undefined depending on that very test holds the something.
   */
  private settled(value: Value): Value {
    while (value.k === "choice") {
      const cond = value.cond
      if (this.pc.some(known => ir.same(known, cond))) value = value.a
      else {
        const negated = ir.not(cond)
        if (this.pc.some(known => ir.same(known, negated))) value = value.b
        else break
      }
    }
    return value
  }

  /**
   * `a === b` for two values. Values of different kinds are never equal, and
   * a number is a different kind from a bigint even when both are whole.
   */
  private strictEqual(a: Value, b: Value, at: Node): Expr {
    if (a.k === "void" || b.k === "void") return a.k === b.k ? ir.TRUE : this.isPlain(a) && this.isPlain(b) ? ir.FALSE : this.refuseEquality(a, b, at)
    if (a.k !== "scalar" || b.k !== "scalar") return this.refuseEquality(a, b, at)
    return a.e.ty === b.e.ty && !!a.num === !!b.num ? ir.eq(a.e, b.e) : ir.FALSE
  }

  private isPlain(value: Value): boolean {
    return value.k === "scalar" || value.k === "void"
  }

  private refuseEquality(a: Value, b: Value, at: Node): never {
    throw new Unsupported(`comparing ${describe(a)} with ${describe(b)} is not modeled; only booleans, bigints, numbers, strings and undefined are compared by ===`, at)
  }

  private binary(node: N, env: Env): Value {
    const operator = node.operatorToken.kind
    if (operator === K.AmpersandAmpersandToken || operator === K.BarBarToken) {
      const isAnd = operator === K.AmpersandAmpersandToken
      const left = this.bool(node.left, env)
      if (left.t === "lit" && left.value !== isAnd) return scalar(left)
      const right = this.under(isAnd ? left : ir.not(left), () => this.unchanging(`the right side of \`${isAnd ? "&&" : "||"}\``, node.right, () => this.bool(node.right, env)))
      return scalar(isAnd ? ir.and(left, right) : ir.or(left, right))
    }
    const leftValue = this.evalExpr(node.left, env)
    const rightValue = this.evalExpr(node.right, env)
    if (operator === K.EqualsEqualsEqualsToken || operator === K.ExclamationEqualsEqualsToken) {
      const equal = this.over(leftValue, left => this.over(rightValue, right => scalar(this.strictEqual(left, right, node))))
      const same = this.scalarOf(equal, node, "bool")
      return scalar(operator === K.EqualsEqualsEqualsToken ? same : ir.not(same))
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
        const refusal = () => new Unsupported("an array can only be indexed by a position that is known here", node)
        if (!isNumber(position) || position.k !== "scalar") throw refusal()
        const item = object.items[Number(this.settle(position.e, refusal).value)]
        if (!item) throw new Unsupported("this index is outside the array", node)
        return item
      }
      if (object.k !== "record") throw new Unsupported(`indexing ${describe(object)} is not supported`, node)
      const key = this.scalarOf(this.evalExpr(index, env), index, "str")
      if (key.t === "lit") {
        const field = object.fields.get(key.value as string)
        if (!field || key.value === "__proto__") throw new Unsupported(`property \`${key.value}\` does not exist on this object`, node)
        return field
      }
      // The key is compared with every property name. A key that matches none
      // would read `undefined`, which is not modeled, so that case must be
      // proved impossible. The key's declared type is not trusted for this: a
      // cast can make it claim anything.
      const names = [...object.fields.keys()]
      const pick = (i: number): Value => {
        if (i === names.length) {
          this.emit("missing", ir.FALSE, node)
          return BOTTOM
        }
        return this.branch(ir.eq(key, ir.lit(names[i]!)), () => object.fields.get(names[i]!)!, () => pick(i + 1))
      }
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
      this.assertBuiltinsIntact(node)
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
        if (receiver.k === "scalar" && method === "toString" && node.arguments.length === 0) {
          this.assertBuiltinsIntact(node)
          return this.text(receiver, node)
        }
        if (receiver.k === "array") {
          this.assertBuiltinsIntact(node)
          return this.arrayMethod(receiver, method, args(), node)
        }
        if (receiver.k === "record" && receiver.fields.has(method)) return this.call(receiver.fields.get(method)!, args(), node)
        throw new Unsupported(`calling \`.${method}\` on ${describe(receiver)} is not supported`, node)
      })
    }
    return this.call(this.evalExpr(callee, env), args(), node)
  }

  /** The `Math` functions that keep whole numbers whole. */
  /**
   * Refuse to model a built-in if any file of the program writes to one, as
   * in `Math.abs = ...` or a patched prototype: the name would no longer mean
   * what the model assumes. Installed packages are not examined.
   */
  private assertBuiltinsIntact(use: Node) {
    if (this.tampering === null) {
      this.tampering = undefined
      const builtins = new Set(["Math", "Object", "Array", "String", "Number", "BigInt", "Boolean", "JSON", "Reflect", "Function", "Symbol", "globalThis"])
      const rootOf = (node: N): N => {
        while (node.kind === K.PropertyAccessExpression || node.kind === K.ElementAccessExpression || node.kind === K.ParenthesizedExpression ||
          node.kind === K.AsExpression || node.kind === K.NonNullExpression) node = node.expression
        return node
      }
      const visit = (node: N) => {
        if (this.tampering) return
        const assigns = node.kind === K.BinaryExpression && node.operatorToken.kind >= K.FirstAssignment && node.operatorToken.kind <= K.LastAssignment
        const target = assigns ? node.left : node.kind === K.DeleteExpression ? node.expression
          : (node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) && (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken) ? node.operand : undefined
        const root = target && target.kind !== K.Identifier ? rootOf(target) : undefined
        // Also catch a built-in handed to something that writes to it, as in Object.assign(Math, ...) or
        // Object.defineProperty(Array.prototype, ...). Passing one as a value, as in `.map(String)`, is not a write.
        const writes = node.kind === K.CallExpression && WRITERS.test(node.expression.getText(node.getSourceFile()))
        const handed = writes ? (node.arguments as N[]).slice(0, 1).map(rootOf).find(a => a.kind === K.Identifier && builtins.has(a.text)) : undefined
        const culprit = root?.kind === K.Identifier && builtins.has(root.text) ? root : handed
        if (culprit && this.isBuiltin(culprit)) {
          const at = locate(node)
          this.tampering = { message: `\`${culprit.text}\` is modified at ${at.file}:${at.line}, so built-in behaviour cannot be assumed`, node }
          return
        }
        node.forEachChild(visit)
      }
      for (const name of this.program.getSourceFileNames()) {
        const file = this.program.getSourceFile(name)
        if (file && !file.isDeclarationFile && !this.program.isSourceFileFromExternalLibrary(file)) visit(file)
      }
    }
    if (this.tampering) throw new Unsupported(this.tampering.message, use)
  }

  private math(name: string, node: N, env: Env): Value {
    this.assertBuiltinsIntact(node)
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
      if (name === "trunc") return scalar(ir.div(a, b), true)
      // The ceiling of a quotient is the negated floor of its negation.
      return scalar(name === "floor" ? ir.fdiv(a, b) : ir.neg(ir.fdiv(ir.neg(a), b)), true)
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

  private arrayMethod(array: Extract<Value, { k: "array" }>, method: string, args: Value[], node: N): Value {
    const items = array.items
    if (method === "push") {
      for (const value of args) {
        this.assertChangeable(array, value, node)
        this.write(array, items.length, value)
      }
      return scalar(ir.lit(BigInt(items.length)), true)
    }
    if (ARRAY_MUTATORS.has(method)) throw new Unsupported(`\`.${method}\` changes the array in place in a way that is not modeled; only \`.push\` and assigning to a position are`, node)
    if (!["includes", "some", "every", "map", "reduce"].includes(method)) throw new Unsupported(`the array method \`.${method}\` is not supported`, node)
    const [first, second] = args
    const expected = method === "reduce" ? 2 : 1
    if (!first || args.length !== expected) {
      throw new Unsupported(method === "reduce" ? "`.reduce` is supported with a callback and an initial value" : `\`.${method}\` is supported with exactly one argument`, node)
    }
    // A callback is passed each element and its position. One that declares
    // more parameters would also receive the array itself, which is refused.
    const invoke = (fn: Value, values: Value[]): Value => {
      if (fn.k === "choice") return this.branch(fn.cond, () => invoke(fn.a, values), () => invoke(fn.b, values))
      if (fn.k === "closure" && parametersOf(fn.node).length > values.length) throw new Unsupported("an array callback that takes the array itself is not supported", node)
      return this.call(fn, values, node)
    }
    const callable = (fn: Value): boolean => fn.k === "closure" || (fn.k === "choice" && callable(fn.a) && callable(fn.b))
    if (method !== "includes" && !callable(first)) throw new Unsupported(`\`.${method}\` needs a function, but this is ${describe(first)}`, node)
    const position = (index: number) => scalar(ir.lit(BigInt(index)), true)
    switch (method) {
      case "reduce":
        return items.reduce((accumulator, item, index) => invoke(first, [accumulator, item, position(index)]), second!)
      case "includes": {
        return scalar(items.map(item => this.scalarOf(this.over(item, element => this.over(first, needle => scalar(this.strictEqual(element, needle, node)))), node, "bool"))
          .reduce(ir.or, ir.FALSE))
      }
      case "some":
      case "every": {
        // JavaScript stops at the first element that settles the answer; the model asks every element.
        const results = this.unchanging(`a callback of \`.${method}\``, node, () => items.map((item, index) => this.scalarOf(invoke(first, [item, position(index)]), node, "bool")))
        return scalar(method === "some" ? results.reduce(ir.or, ir.FALSE) : results.reduce(ir.and, ir.TRUE))
      }
      case "map":
        return this.fresh({ k: "array", items: items.map((item, index) => invoke(first, [item, position(index)])) })
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
      // While a module loads, its constants are initialized in order. Code
      // that runs during one initializer cannot read a constant declared
      // further down the same file: JavaScript throws there.
      const early = this.loading.find(entry => entry.file === file.fileName && declaration.pos > entry.position)
      if (early) throw new Unsupported(`\`${node.text}\` is read while its module is loading, before its own declaration has run, which throws`, node)
      const known = this.constants.get(declaration)
      if (known) return known
      // The initializer runs once, in an epoch of its own: it may build its value step by step, and nothing after it may change that value.
      const saved = { pc: this.pc, stack: this.stack, instance: this.instance, cells: this.cells, assigned: this.assigned, epoch: this.epoch }
      this.epoch = ++epochs
      this.pc = []
      this.stack = []
      this.instance = undefined
      this.cells = []
      this.assigned = []
      this.loading.push({ file: file.fileName, position: declaration.pos })
      try {
        const value = this.evalExpr(declaration.initializer, new Env())
        if (value.k !== "scalar" && value.k !== "closure") this.assertStable(file, declaration, value, node)
        this.constants.set(declaration, value)
        return value
      } finally {
        this.loading.pop()
        Object.assign(this, saved)
      }
    }
    throw new Unsupported(`\`${node.text}\` is declared in a way that is not supported (only functions and const values are)`, node)
  }

  /**
   * Refuse a module constant whose contents may differ from its initializer
   * by the time a law runs. Only two kinds of code run before then: the
   * module's own loading, and whatever the law calls (which is translated,
   * and refused if it changes a module constant in place). So the value is stable
   * unless the file changes it by name, hands it to something while loading,
   * or runs its own functions while loading.
   */
  private assertStable(file: SourceFile, declaration: N, value: Value, use: Node) {
    const name = declaration.name.text as string
    const key = `${file.fileName}\0${name}`
    if (this.mutationChecked.has(key)) return
    const refuse = (reason: string, at: N): never => {
      throw new Unsupported(`\`${name}\` ${reason} at line ${locate(at).line} of its module, so its initial value cannot be assumed`, use)
    }
    this.assertBuiltinsIntact(use)
    const loose = (file.statements as readonly N[]).find(statement => !MODULE_DECLARATIONS.has(statement.kind))
    if (loose) refuse("shares its module with a statement that runs on load", loose)
    const isFunction = (node: N) => node.kind === K.ArrowFunction || node.kind === K.FunctionExpression || node.kind === K.FunctionDeclaration ||
      node.kind === K.MethodDeclaration || node.kind === K.GetAccessor || node.kind === K.SetAccessor || node.kind === K.Constructor
    const unwrap = (node: N): N => {
      while (node.kind === K.ParenthesizedExpression || node.kind === K.AsExpression || node.kind === K.SatisfiesExpression || node.kind === K.NonNullExpression) node = node.expression
      return node
    }
    // Functions of this file that its own loading can run.
    const local = new Set<string>()
    for (const statement of file.statements as readonly N[]) {
      if (statement.kind === K.FunctionDeclaration && statement.name) local.add(statement.name.text)
      if (statement.kind === K.VariableStatement) {
        for (const d of statement.declarationList.declarations as N[]) {
          if (d.name.kind === K.Identifier && d.initializer && isFunction(unwrap(d.initializer))) local.add(d.name.text)
        }
      }
    }
    const isLocalCode = (node: N) => {
      const inner = unwrap(node)
      return isFunction(inner) || (inner.kind === K.Identifier && local.has(inner.text))
    }
    // Names this file imports. Only a function reached through one of them counts as a library.
    const imported = new Set<string>()
    for (const statement of file.statements as readonly N[]) {
      const clause = statement.kind === K.ImportDeclaration ? statement.importClause : undefined
      if (clause?.name) imported.add(clause.name.text)
      if (clause?.namedBindings?.kind === K.NamespaceImport) imported.add(clause.namedBindings.name.text)
      if (clause?.namedBindings?.kind === K.NamedImports) for (const element of clause.namedBindings.elements as N[]) imported.add(element.name.text)
    }
    const fromPackage = (callee: N): boolean => {
      let root = unwrap(callee)
      while (root.kind === K.PropertyAccessExpression || root.kind === K.ElementAccessExpression || root.kind === K.CallExpression) root = unwrap(root.expression)
      if (root.kind !== K.Identifier || !imported.has(root.text)) return false
      let symbol = this.checker.getSymbolAtLocation(root)
      if (symbol && symbol.flags & SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol)
      const source = symbol?.declarations[0]?.resolve()?.getSourceFile()
      return !!source && this.program.isSourceFileFromExternalLibrary(source)
    }
    const shallow = (value: Value | undefined) =>
      value?.k === "record" ? [...value.fields.values()].every(field => field.k === "scalar")
        : value?.k === "array" ? value.items.every(item => item.k === "scalar") : false
    // Whether the whole initializer is asserted `as const`, read from the
    // syntax: the words may also appear on a single field or in a comment,
    // which says nothing about the table.
    const declaredConst = ((): boolean => {
      for (let node: N = declaration.initializer; ; node = node.expression) {
        if (node.kind === K.AsExpression) {
          const type = node.type as N
          if (type.kind === K.TypeReference && type.typeName.kind === K.Identifier && type.typeName.text === "const" && !type.typeArguments?.length) return true
        } else if (node.kind !== K.ParenthesizedExpression && node.kind !== K.SatisfiesExpression && node.kind !== K.NonNullExpression) return false
      }
    })()
    const handedOver: { at: N; inFunction: boolean }[] = []
    const visit = (node: N, inFunction: boolean) => {
      if (node.kind === K.Identifier && node.text === name && node !== declaration.name) {
        // The longest access path that starts at this name, such as `table.rows[0]`.
        let top = node
        const path: (string | undefined)[] = []
        while ((top.parent.kind === K.PropertyAccessExpression || top.parent.kind === K.ElementAccessExpression) && top.parent.expression === top) {
          top = top.parent
          path.push(top.kind === K.PropertyAccessExpression ? top.name.text : top.argumentExpression.kind === K.StringLiteral || top.argumentExpression.kind === K.NumericLiteral ? top.argumentExpression.text : undefined)
        }
        let outer = top
        while (outer.parent.kind === K.ParenthesizedExpression || outer.parent.kind === K.AsExpression || outer.parent.kind === K.SatisfiesExpression || outer.parent.kind === K.NonNullExpression) outer = outer.parent
        const parent = outer.parent
        const assigned = parent.kind === K.BinaryExpression && parent.left === outer &&
          parent.operatorToken.kind >= K.FirstAssignment && parent.operatorToken.kind <= K.LastAssignment
        const updated = (parent.kind === K.PrefixUnaryExpression || parent.kind === K.PostfixUnaryExpression) &&
          (parent.operator === K.PlusPlusToken || parent.operator === K.MinusMinusToken)
        const called = parent.kind === K.CallExpression && parent.expression === outer && top.kind === K.PropertyAccessExpression
        if (assigned || updated || parent.kind === K.DeleteExpression || (called && ARRAY_MUTATORS.has(top.name.text))) refuse("is modified", parent)
        // Reading through the value is harmless. What matters is where the
        // value itself, or an object inside it, is handed to other code.
        // Everything the path can lead to. A key that is not a literal can pick any child.
        let reached: Value[] = [value]
        for (const step of path.slice(0, called ? -1 : undefined)) {
          reached = reached.flatMap(part => {
            // The length of a list is a plain number.
            if (step === "length" && part.k === "array") return [scalar(ir.lit(BigInt(part.items.length)), true)]
            const children = part.k === "record" ? [...part.fields] : part.k === "array" ? part.items.map((item, i) => [String(i), item] as [string, Value]) : []
            return children.filter(([key]) => step === undefined || key === step).map(([, child]) => child)
          })
        }
        const plain = reached.length > 0 && reached.every(part => part.k === "scalar")
        const flat = reached.length > 0 && reached.every(shallow)
        // Only uses that are known to read count as reads. A method call does
        // when it is one of the array methods that change nothing, on a list
        // of plain values; a method the table defines itself may do anything.
        // Spreading and iterating copy one level, so they are reads when that
        // level holds no objects. `a ?? b` and the like return the table itself.
        const compares = parent.kind === K.BinaryExpression &&
          [K.EqualsEqualsEqualsToken, K.ExclamationEqualsEqualsToken, K.EqualsEqualsToken, K.ExclamationEqualsToken, K.InKeyword].includes(parent.operatorToken.kind)
        const reads = (called && READING_METHODS.has(top.name.text) && flat) || (!called && plain) ||
          parent.kind === K.TypeQuery || parent.kind === K.TypeOfExpression || parent.kind === K.ExportSpecifier || parent.kind === K.ExportAssignment ||
          ((parent.kind === K.SpreadElement || parent.kind === K.SpreadAssignment || (parent.kind === K.ForOfStatement && parent.expression === outer)) && flat) ||
          compares
        // A value declared `as const` may be given to an installed package
        // while loading: its type forbids changing it, and schema builders are
        // the common case. A function of the project itself gets no such trust.
        const toLibrary = declaredConst && parent.kind === K.CallExpression && parent.expression !== outer && fromPackage(parent.expression)
        // A built-in that only reads may be given the table anywhere.
        const callee = (parent.kind === K.CallExpression || parent.kind === K.NewExpression) && parent.expression !== outer ? parent.expression.getText(file) : ""
        const toReader = READERS.test(callee) || (flat && (SHALLOW_READERS.test(callee) || (parent.kind === K.NewExpression && /^(Set|Map)$/.test(callee))))
        if (!reads && !toLibrary && !toReader) handedOver.push({ at: parent, inFunction })
      }
      node.forEachChild((child: N) => visit(child, inFunction || isFunction(child)))
    }
    visit(file, false)
    const atLoad = handedOver.find(entry => !entry.inFunction)
    if (atLoad) refuse("is handed to other code while its module loads", atLoad.at)
    // A function that hands the table on could be run while some module loads,
    // by this module or by another that imports it, and nothing here can tell.
    const inCode = handedOver.find(entry => entry.inFunction)
    if (inCode) refuse("is handed to other code by a function, which may run before the law does,", inCode.at)
    this.mutationChecked.add(key)
  }
}

/** A function's parameters as they exist at run time: TypeScript's `this` parameter is erased. */
function parametersOf(fn: N): N[] {
  return (fn.parameters as N[]).filter(parameter => !(parameter.name.kind === K.Identifier && parameter.name.text === "this"))
}

/** The names a binding pattern declares. */
function boundNames(pattern: N, into: string[] = []): string[] {
  if (pattern.kind === K.Identifier) into.push(pattern.text)
  else for (const element of (pattern.elements ?? []) as N[]) if (element.name) boundNames(element.name, into)
  return into
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
