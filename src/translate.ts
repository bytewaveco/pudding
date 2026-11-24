import {
  ElementFlags,
  NodeFlags,
  SignatureKind,
  SymbolFlags,
  SyntaxKind as K,
  TypeFlags,
  type Checker,
  type Node,
  type Program,
  type SourceFile,
  type Type,
} from './compiler.ts'
import * as ir from './ir.ts'

import type { Binder, Expr, Obligation, ObligationKind, Scalar, Ty } from './ir.ts'

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

class NeedsValue extends Error {
  readonly inputs: Set<string>
  readonly refusal: Unsupported
  constructor(inputs: Set<string>, refusal: Unsupported) {
    super(refusal.message)
    this.inputs = inputs
    this.refusal = refusal
  }
}

export type ArgShape =
  | { k: 'binder'; name: string }
  | { k: 'const'; value: Scalar; num?: boolean }
  | { k: 'record'; fields: [string, ArgShape][] }
  | { k: 'array'; items: ArgShape[] }
  | { k: 'undefined' }
  | { k: 'null' }

export interface LawInstance {
  assumptions: Expr[]
  fixed: Map<string, Expr>
  binders: Binder[]
  arg: ArgShape | undefined
  obligations: Obligation[]
  defs?: ir.FnDef[]
}

export interface Law {
  name: string
  file: string
  line: number
  column: number
  index: number
  mode: 'run' | 'skip' | 'todo'
  proof: string | undefined
  instances: LawInstance[]
  mentioned: Expr[]
  expectSites: Map<string, { file: string; line: number; column: number; text: string }>
  narrowed?: boolean
  problem: ({ kind: 'unsupported' | 'invalid'; message: string } & Location) | undefined
}

type Value =
  | { k: 'scalar'; e: Expr; num?: boolean }
  | { k: 'rat'; num: Expr; shift: number }
  | { k: 'quot'; num: Expr; den: Expr }
  | { k: 'float'; value: number }
  | { k: 'list'; e: Expr; num?: boolean }
  | { k: 'record'; fields: Map<string, Value>; own?: Ownership; unordered?: boolean }
  | { k: 'array'; items: Value[]; own?: Ownership }
  | { k: 'closure'; node: N; env: Env }
  | { k: 'choice'; cond: Expr; a: Value; b: Value }
  | { k: 'bottom' }
  | { k: 'void' }
  | { k: 'null' }
  | { k: 'infinite'; negative: boolean }
  | { k: 'map'; log: Extract<Value, { k: 'array' }> }
  | { k: 'set'; log: Extract<Value, { k: 'array' }> }
  | {
      k: 'iterator'
      source: Extract<Value, { k: 'map' | 'set' }>
      mode: 'keys' | 'values' | 'entries'
      state: Extract<Value, { k: 'record' }>
    }
  | { k: 'tombstone' }
  | { k: 'uninitialized' }

type Stored = Extract<Value, { k: 'record' | 'array' }>

interface Ownership {
  epoch: number
  born: number
}

interface Write {
  target: Stored
  slot: string | number
  previous: Value | undefined
}

type Changes = Map<Stored, Map<string | number, Value | undefined>>

let epochs = 0
let objectsCreated = 0

type Shape =
  | { k: 'scalar'; ty: Ty; values?: Scalar[]; num?: boolean; range?: [bigint, bigint] }
  | { k: 'list'; elem: ir.ScalarTy; num?: boolean; range?: [bigint, bigint] }
  | { k: 'record'; fields: [string, Shape][] }
  | { k: 'tuple'; items: Shape[] }
  | { k: 'union'; alts: Shape[] }
  | { k: 'void' }
  | { k: 'null' }
  | { k: 'absent' }

interface Cell {
  value: Value
  readonly mutable: boolean
}

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
  revert(name: string, previous: Cell | undefined) {
    if (previous) this.vars.set(name, previous)
    else this.vars.delete(name)
  }
  child() {
    return new Env(this)
  }
  mutableCells(into = new Map<string, Cell | undefined>()): Map<string, Cell | undefined> {
    for (const [name, cell] of this.vars)
      if (!into.has(name)) into.set(name, cell.mutable ? cell : undefined)

    return this.parent ? this.parent.mutableCells(into) : into
  }
}

interface Saved {
  values: Value[]
  logged: number
  scopes: number
  written: number
  frozen: number
  objects: number
  closures: number
}

interface Flow {
  next: () => Value
  brk?: () => Value
  cont?: () => Value
}

const BOTTOM: Value = { k: 'bottom' }
const VOID: Value = { k: 'void' }
const NULL: Value = { k: 'null' }
const TOMBSTONE: Value = { k: 'tombstone' }
const UNINITIALIZED: Value = { k: 'uninitialized' }
const MAX_STEPS = 200_000
let syntaxTables:
  | { compound: Map<number, number>; moduleDecl: Set<number>; noValueDecl: Set<number> }
  | undefined

function tables() {
  if (!syntaxTables) {
    syntaxTables = {
      compound: new Map<number, number>([
        [K.PlusEqualsToken, K.PlusToken],
        [K.MinusEqualsToken, K.MinusToken],
        [K.AsteriskEqualsToken, K.AsteriskToken],
        [K.SlashEqualsToken, K.SlashToken],
        [K.PercentEqualsToken, K.PercentToken],
      ]),
      moduleDecl: new Set<number>([
        K.ImportDeclaration,
        K.ExportDeclaration,
        K.ExportAssignment,
        K.VariableStatement,
        K.FunctionDeclaration,
        K.ClassDeclaration,
        K.InterfaceDeclaration,
        K.TypeAliasDeclaration,
        K.EnumDeclaration,
        K.ModuleDeclaration,
        K.ImportEqualsDeclaration,
        K.EmptyStatement,
      ]),
      noValueDecl: new Set<number>([
        K.ImportDeclaration,
        K.InterfaceDeclaration,
        K.TypeAliasDeclaration,
        K.EmptyStatement,
      ]),
    }
  }

  return syntaxTables
}

const scalar = (e: Expr, num = false): Value => (num ? { k: 'scalar', e, num } : { k: 'scalar', e })
const isNumber = (value: Value) => value.k === 'scalar' && value.num === true

const isNumeric = (value: Value) =>
  isNumber(value) || value.k === 'rat' || value.k === 'quot' || value.k === 'float'

const MAX_DYADIC_SHIFT = 10

function dyadicOf(value: number): { num: bigint; shift: number } | undefined {
  if (!Number.isFinite(value) || Number.isSafeInteger(value)) return undefined

  for (let shift = 1; shift <= MAX_DYADIC_SHIFT; shift++) {
    const scale = 2 ** shift
    const scaled = value * scale

    if (Number.isSafeInteger(scaled) && scaled / scale === value)
      return { num: BigInt(scaled), shift }
  }

  return undefined
}

function pow2Of(d: bigint): { negative: boolean; shift: number } | undefined {
  if (d === 0n) return undefined
  const negative = d < 0n
  const mag = negative ? -d : d
  if ((mag & (mag - 1n)) !== 0n) return undefined
  let shift = 0
  let v = mag

  while (v > 1n) {
    v >>= 1n
    shift++
  }

  return shift <= MAX_DYADIC_SHIFT ? { negative, shift } : undefined
}

const MAX_ENUMERATED_RANGE = 256n
const MAX_ITERATIONS = 2_000
const MAX_INSTANCES = 256
const NUMBER_HELP =
  '`number` covers fractions, NaN and infinities, which are not modeled; use `Integer` from pudding for whole numbers, or bigint'
const MAX_ALTERNATIVES = 64
const MAX_TYPE_DEPTH = 24
const MAX_SORTED = 64
const MAX_SHAPES = 10_000
const MAX_UNDECIDED = 8

function isArrayIndexKey(key: string): boolean {
  if (!/^(0|[1-9]\d*)$/.test(key)) return false
  const n = Number(key)
  return n >= 0 && n <= 0xfffffffe
}

function ownKeysOrdered(fields: Map<string, Value>): string[] {
  const indices: string[] = []
  const rest: string[] = []
  for (const key of fields.keys()) (isArrayIndexKey(key) ? indices : rest).push(key)
  indices.sort((a, b) => Number(a) - Number(b))
  return [...indices, ...rest]
}

const READING_METHODS = new Set([
  'includes',
  'indexOf',
  'lastIndexOf',
  'join',
  'slice',
  'concat',
  'at',
  'flat',
  'keys',
  'values',
  'entries',
  'toString',
  'toReversed',
  'toSorted',
  'toSpliced',
  'with',
])
const CALLBACK_READING_METHODS = new Set([
  'some',
  'every',
  'map',
  'reduce',
  'reduceRight',
  'filter',
  'find',
  'findIndex',
  'findLast',
  'findLastIndex',
  'flatMap',
])
const WRITERS =
  /^(Object\.(assign|defineProperty|defineProperties|setPrototypeOf)|Reflect\.(set|defineProperty|setPrototypeOf|deleteProperty))$/
const READERS =
  /^(Object\.(keys|isFrozen|hasOwn|getOwnPropertyNames)|Array\.isArray|JSON\.stringify|String|Boolean)$/
const SHALLOW_READERS =
  /^(Object\.(values|entries|freeze|fromEntries)|Array\.from|structuredClone)$/
const ARRAY_MUTATORS = new Set([
  'push',
  'pop',
  'shift',
  'unshift',
  'splice',
  'sort',
  'reverse',
  'fill',
  'copyWithin',
  'set',
  'delete',
  'clear',
  'add',
])

export function locate(node: Node): Location {
  const file = node.getSourceFile()
  const at = file.getLineAndCharacterOfPosition(node.getStart(file))
  return { file: file.fileName, line: at.line + 1, column: at.character + 1 }
}

function sourceText(node: Node): string {
  const text = node.getText(node.getSourceFile()).replace(/\s+/g, ' ')
  return text.length > 140 ? text.slice(0, 137) + '...' : text
}

function describe(value: Value): string {
  switch (value.k) {
    case 'scalar':
      return value.num
        ? 'a number'
        : { bool: 'a boolean', int: 'a bigint', str: 'a string' }[value.e.ty as ir.ScalarTy]
    case 'rat':
    case 'quot':
    case 'float':
      return 'a number'
    case 'record':
      return 'an object'
    case 'array':
    case 'list':
      return 'an array'
    case 'closure':
      return 'a function'
    case 'choice':
      return 'a value that depends on a condition'
    case 'bottom':
      return 'a thrown error'
    case 'void':
      return 'nothing'
    case 'null':
      return 'null'
    case 'infinite':
      return 'Infinity'
    case 'map':
      return 'a Map'
    case 'set':
      return 'a Set'
    case 'iterator':
      return 'an iterator'
    case 'tombstone':
      return 'a deleted entry'
    case 'uninitialized':
      return 'a variable that is not initialized yet'
  }
}

export class Translator {
  readonly reached = new Set<string>()
  readonly fileReached = new Map<string, Set<string>>()
  private activeReached: Set<string> | undefined
  private readonly checker: Checker
  private readonly program: Program
  private readonly moduleName: string
  private readonly constants = new Map<Node, Value>()
  private readonly mutationChecked = new Set<string>()
  private stack: N[] = []
  private pc: Expr[] = []
  private cells: Cell[] = []
  private shapes = 0
  private frame = 0
  private assignedTo: Set<Cell> | undefined
  private writtenTo: Set<Stored> | undefined
  private assigned: Set<string>[] = []
  private steps = 0
  private merging = 0
  private loading: { file: string; position: number }[] = []
  private mentioned: Expr[] = []
  private sites: Law['expectSites'] | undefined
  private scanned = new Set<Node>()
  private readonly importing = new Map<string, boolean>()
  private readonly exportsUsed = new Map<Node, string>()
  private tampering: { message: string; node: Node } | undefined | null = null
  private epoch = 0
  private writes: Write[] = []
  private freezes: { target: Stored; epoch: number }[] = []
  private readonly activeIterators = new Set<Stored>()
  private inThrowCheck = 0
  private closuresCreated = 0
  private lambdaCounter = 0
  private compilingFns = new Map<
    N,
    {
      name: string
      params: { name: string; ty: Ty; num?: boolean }[]
      retTy: Ty
      retNum?: boolean
      calls: Expr[][]
    }
  >()
  private compiledFns = new Map<string, ir.FnDef>()
  private fnNodeIds = new WeakMap<object, number>()
  private nextFnNodeId = 0
  private readonly facts = new Map<
    Node,
    {
      assigned: Set<string>
      mentioned: Set<string>
      returnsValue: boolean
      usesVar: Node | undefined
      isRecursive: boolean
    }
  >()
  private instance: LawInstance | undefined

  constructor(program: Program, checker: Checker, moduleName: string) {
    this.program = program
    this.checker = checker
    this.moduleName = moduleName
  }

  translateFile(file: SourceFile, selected: (name: string) => boolean = () => true): Law[] {
    this.reached.add(file.fileName)
    this.activeReached?.add(file.fileName)
    const deps = new Set<string>([file.fileName])
    this.fileReached.set(file.fileName, deps)
    this.activeReached = deps
    const laws: (Law & { only?: boolean })[] = []

    try {
      this.translateBlock(file.statements as readonly N[], undefined, [], 'run', laws, selected)

      if (laws.some((law) => law.only))
        for (const law of laws) if (!law.only && law.mode === 'run') this.skip(law)

      return laws
    } finally {
      this.activeReached = undefined
    }
  }

  private skip(law: Law) {
    law.mode = 'skip'
    law.instances = []
    law.problem = undefined
  }

  private testCall(
    node: N,
  ): { kind: 'law' | 'describe'; modifier: string | undefined } | undefined {
    if (node?.kind !== K.CallExpression) return undefined
    let callee = node.expression
    let modifier: string | undefined

    if (callee.kind === K.PropertyAccessExpression && callee.expression.kind === K.Identifier) {
      modifier = callee.name.text
      callee = callee.expression
    }

    if (callee.kind !== K.Identifier) return undefined
    const name = this.libraryExport(callee)
    return name === 'law' || name === 'describe' ? { kind: name, modifier } : undefined
  }

  private libraryExport(identifier: N): string | undefined {
    let known = this.exportsUsed.get(identifier)

    if (known === undefined) {
      const declaration = this.checker
        .getSymbolAtLocation(identifier)
        ?.declarations[0]?.resolve() as N
      known =
        declaration?.kind === K.ImportSpecifier &&
        declaration.parent.parent.parent.moduleSpecifier.text === this.moduleName
          ? ((declaration.propertyName ?? declaration.name).text as string)
          : ''
      this.exportsUsed.set(identifier, known)
    }

    return known || undefined
  }

  private translateBlock(
    statements: readonly N[],
    env: Env | undefined,
    path: string[],
    mode: 'run' | 'skip' | 'only',
    laws: (Law & { only?: boolean })[],
    selected: (name: string) => boolean,
  ) {
    if (env) this.enter(statements, env)

    const invalid = (statement: N, message: string) =>
      laws.push({
        name: sourceText(statement),
        ...locate(statement),
        index: -1,
        mode: 'run',
        proof: undefined,
        instances: [],
        mentioned: [],
        expectSites: new Map(),
        problem: { kind: 'invalid', message, ...locate(statement) },
      })

    for (const statement of statements) {
      if (statement.kind !== K.ExpressionStatement) {
        if (!env && !tables().moduleDecl.has(statement.kind))
          invalid(
            statement,
            'only law() and describe() calls and declarations are allowed in a law file',
          )

        if (!env || tables().noValueDecl.has(statement.kind)) continue

        try {
          this.writes = []
          this.freezes = []
          this.epoch = ++epochs

          if (statement.kind === K.VariableStatement) this.declare(statement, env)
          else if (statement.kind !== K.FunctionDeclaration)
            invalid(statement, 'only laws and declarations are allowed inside describe()')
        } catch (error) {
          if (!(error instanceof Unsupported)) throw error
          invalid(error.node ?? statement, error.message)
        }

        continue
      }

      const call = statement.expression
      const test = this.testCall(call)

      if (!test) {
        invalid(
          statement,
          'only law() and describe() calls and declarations are allowed in a law file',
        )
        continue
      }

      const { modifier } = test

      if (
        modifier !== undefined &&
        modifier !== 'skip' &&
        modifier !== 'only' &&
        !(modifier === 'todo' && test.kind === 'law')
      ) {
        invalid(
          statement,
          `\`.${modifier}\` is not a modifier Pudding knows; use .skip, .only or .todo`,
        )
        continue
      }

      const own =
        modifier === 'skip' || mode === 'skip'
          ? 'skip'
          : modifier === 'only' || mode === 'only'
            ? 'only'
            : 'run'
      const nameNode = call.arguments[0]

      if (
        nameNode?.kind !== K.StringLiteral &&
        nameNode?.kind !== K.NoSubstitutionTemplateLiteral
      ) {
        invalid(statement, `the first argument of ${test.kind}() must be a string literal`)
        continue
      }

      if (test.kind === 'describe') {
        const body = call.arguments[1]

        if (
          (body?.kind !== K.ArrowFunction && body?.kind !== K.FunctionExpression) ||
          body.body.kind !== K.Block ||
          body.parameters.length
        ) {
          invalid(statement, 'describe() takes a name and a callback with a block body')
          continue
        }

        this.translateBlock(
          body.body.statements,
          (env ?? new Env()).child(),
          [...path, nameNode.text],
          own,
          laws,
          selected,
        )
        continue
      }

      const name = [...path, nameNode.text].join(' > ')
      const index = laws.filter((law) => law.index >= 0).length

      if (modifier === 'todo' || own === 'skip' || !selected(name)) {
        laws.push({
          name,
          ...locate(call),
          index,
          mode: modifier === 'todo' ? 'todo' : 'skip',
          proof: undefined,
          instances: [],
          mentioned: [],
          expectSites: new Map(),
          problem: undefined,
          ...(own === 'only' && modifier !== 'todo' ? { only: true } : {}),
        })
        continue
      }

      const law: Law & { only?: boolean } = this.translateLaw(call, index, name, env)
      if (own === 'only') law.only = true
      laws.push(law)
    }
  }

  private isCallTo(node: N, name: string): boolean {
    return (
      node?.kind === K.CallExpression &&
      node.expression.kind === K.Identifier &&
      this.libraryExport(node.expression) === name
    )
  }

  private translateLaw(call: N, index: number, name: string, scope: Env | undefined): Law {
    const args = call.arguments as N[]
    const law: Law = {
      name,
      ...locate(call),
      index,
      mode: 'run',
      proof: undefined,
      instances: [],
      mentioned: [],
      expectSites: new Map(),
      problem: undefined,
    }

    const invalid = (message: string, node: Node) => {
      law.problem = { kind: 'invalid', message, ...locate(node) }
      return law
    }

    const hasDomain = this.isCallTo(args[1], 'domain')
    const callback = args[hasDomain ? 2 : 1]
    const options = args[hasDomain ? 3 : 2]

    if (callback?.kind !== K.ArrowFunction && callback?.kind !== K.FunctionExpression)
      return invalid('law() needs a callback', call)

    if (callback.parameters.length !== (hasDomain ? 1 : 0))
      return invalid(
        hasDomain
          ? 'the callback takes exactly one parameter'
          : 'a law without a domain takes no parameter',
        callback,
      )

    if (callback.asteriskToken || callback.modifiers?.some((m: N) => m.kind === K.AsyncKeyword))
      return invalid('a law callback must be an ordinary synchronous function', callback)

    const [parameter] = callback.parameters as N[]

    if (parameter && (parameter.dotDotDotToken || parameter.initializer || parameter.questionToken))
      return invalid(
        "the callback's parameter must be plain: no rest, default or optional marker",
        parameter,
      )

    if (options) {
      if (options.kind !== K.ObjectLiteralExpression)
        return invalid('law() options must be an object literal', options)

      for (const property of options.properties as N[]) {
        const value = property.initializer

        if (
          property.kind !== K.PropertyAssignment ||
          property.name.text !== 'proof' ||
          (value.kind !== K.StringLiteral && value.kind !== K.NoSubstitutionTemplateLiteral)
        )
          return invalid(
            'the only option is `proof`, a string literal holding a Lean tactic script',
            property,
          )

        law.proof = value.text
      }
    }

    this.scanExpectSites(callback.body, law.expectSites)
    this.mentioned = law.mentioned
    this.sites = law.expectSites

    try {
      let alternatives: Shape[] = [{ k: 'tuple', items: [] }]

      if (hasDomain) {
        const typeNode = args[1].typeArguments?.[0]
        if (!typeNode) return invalid('domain<T>() needs a type argument', args[1])
        const type = this.checker.getTypeFromTypeNode(typeNode)
        if (!type) return invalid('the domain type could not be resolved', typeNode)
        this.shapes = 0
        alternatives = this.expand(this.shapeOf(type, typeNode), typeNode)
      }

      for (const alternative of alternatives) {
        const instance: LawInstance = {
          assumptions: [],
          fixed: new Map(),
          binders: [],
          arg: undefined,
          obligations: [],
        }
        this.instance = instance
        if (hasDomain) instance.arg = this.instantiate(alternative, instance)
        law.instances.push(instance)
      }

      const options = this.program.getCompilerOptions()

      if (hasDomain && !(options.strictNullChecks ?? options.strict ?? true)) {
        law.narrowed = true
        throw new Unsupported(
          'inputs are listed from their types, and without `strictNullChecks` a type does not say whether it holds undefined; turn it on in the tsconfig the laws are read with',
          args[1],
        )
      }

      const waiting = law.instances
      law.instances = []

      while (waiting.length) {
        const instance = waiting.shift()!
        this.instance = instance
        this.pc = [...instance.assumptions]
        this.stack = []
        this.cells = []
        this.frame = 0
        bindingLog.length = 0
        this.writes = []
        this.freezes = []
        this.closuresCreated = 0
        this.compilingFns.clear()
        this.compiledFns.clear()
        this.epoch = ++epochs
        this.steps = 0
        const facts = this.factsOf(callback)

        if (facts.usesVar)
          throw new Unsupported('`var` is not supported; use `const` or `let`', facts.usesVar)

        this.assigned = [facts.assigned]
        const env = scope ? scope.child() : new Env()

        try {
          if (instance.arg) {
            for (const bound of boundNames(callback.parameters[0].name))
              env.set(bound, UNINITIALIZED)

            this.bind(callback.parameters[0].name, this.valueOf(instance.arg), env, true, true)
          }

          const body = callback.body

          if (body.kind === K.Block) this.block(body.statements, env, { next: () => VOID })
          else this.effect(body, env)

          law.instances.push(instance)
        } catch (error) {
          const input =
            error instanceof NeedsValue
              ? instance.binders.find(
                  (b) => error.inputs.has(b.name) && b.domain && b.domain.length > 1,
                )
              : undefined

          if (
            !input ||
            law.instances.length + waiting.length + input.domain!.length > MAX_INSTANCES
          ) {
            law.instances.push(instance, ...waiting)
            throw error instanceof NeedsValue ? error.refusal : error
          }

          waiting.unshift(
            ...input.domain!.map((value) => ({
              ...instance,
              obligations: [],
              binders: instance.binders.map((b) =>
                b === input ? { ...b, domain: [value] } : { ...b },
              ),
              fixed: new Map(instance.fixed).set(input.name, ir.lit(value)),
            })),
          )
        }
      }

      this.assertBuiltinsIntact(call)
      const asserts =
        law.expectSites.size > 0 ||
        law.instances.some((instance) => instance.obligations.some((o) => o.kind === 'expect'))
      if (!asserts) return invalid('the law contains no expect() assertion', callback)
    } catch (error) {
      if (!(error instanceof Unsupported)) throw error
      law.problem = { kind: 'unsupported', message: error.message, ...locate(error.node ?? call) }
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

  private noteExpectations(fn: N) {
    if (!this.sites || this.scanned.has(fn)) return
    this.scanned.add(fn)
    const file = fn.getSourceFile() as SourceFile
    let uses = this.importing.get(file.fileName)

    if (uses === undefined) {
      uses = (file.statements as readonly N[]).some(
        (s) => s.kind === K.ImportDeclaration && s.moduleSpecifier.text === this.moduleName,
      )
      this.importing.set(file.fileName, uses)
    }

    if (uses && fn.body) this.scanExpectSites(fn.body, this.sites)
  }

  private scanExpectSites(root: N, into: Law['expectSites']) {
    while (root.kind === K.ParenthesizedExpression) root = root.expression

    const visit = (n: N) => {
      if (this.isExpect(n)) {
        let statement = n

        while (statement.parent && statement.kind !== K.ExpressionStatement && statement !== root)
          statement = statement.parent

        const at = locate(statement)
        into.set(`${at.file}:${at.line}:${at.column}`, {
          file: at.file,
          line: at.line,
          column: at.column,
          text: sourceText(statement),
        })
      }

      n.forEachChild(visit)
    }

    visit(root)
  }

  private shapeOf(type: Type, at: Node, depth = 0): Shape {
    if (depth > MAX_TYPE_DEPTH)
      throw new Unsupported(
        'this input type is nested too deeply to list its values, or refers to itself',
        at,
      )

    if (++this.shapes > MAX_SHAPES)
      throw new Unsupported(
        `this input type has more than ${MAX_SHAPES} parts, which is too many to list its values`,
        at,
      )

    const flags = type.flags
    const name = () => this.checker.typeToString(type)
    if (flags & TypeFlags.Boolean) return { k: 'scalar', ty: 'bool', values: [true, false] }

    if (flags & TypeFlags.BooleanLiteral)
      return { k: 'scalar', ty: 'bool', values: [name() === 'true'] }

    if (flags & TypeFlags.BigInt) return { k: 'scalar', ty: 'int' }

    if (flags & TypeFlags.BigIntLiteral)
      return { k: 'scalar', ty: 'int', values: [BigInt(name().replace(/n$/, ''))] }

    if (flags & TypeFlags.String) return { k: 'scalar', ty: 'str' }

    if (flags & TypeFlags.StringLiteral)
      return { k: 'scalar', ty: 'str', values: [this.wellFormed(String((type as N).value), at)] }

    if (flags & TypeFlags.NumberLiteral) {
      const value = Number((type as N).value)

      if (!Number.isSafeInteger(value))
        throw new Unsupported(
          `the number ${name()} is not a whole number that can be held exactly`,
          at,
        )

      return { k: 'scalar', ty: 'int', num: true, values: [BigInt(value)] }
    }

    if (flags & TypeFlags.Number) throw new Unsupported(NUMBER_HELP, at)
    if (flags & TypeFlags.Undefined) return { k: 'void' }
    if (flags & TypeFlags.Null) return { k: 'null' }

    if (type.isIntersectionType()) {
      const members = type.getTypes()
      const marker = members
        .map((member) => this.checker.getPropertyOfType(member, '__puddingInteger'))
        .find(Boolean)

      if (marker && members.some((member) => member.flags & TypeFlags.Number)) {
        const carried = this.checker.getTypeOfSymbol(marker)
        const tuple = (carried?.isUnionType() ? carried.getTypes() : carried ? [carried] : []).find(
          (member) => this.checker.isTupleType(member),
        )

        const bound = (member: Type | undefined, fallback: bigint) =>
          member &&
          member.flags & TypeFlags.NumberLiteral &&
          Number.isSafeInteger(Number((member as N).value))
            ? BigInt(Number((member as N).value))
            : fallback

        const [low, high] = tuple ? this.checker.getTypeArguments(tuple as N) : []
        const range: [bigint, bigint] = [bound(low, -ir.MAX_SAFE), bound(high, ir.MAX_SAFE)]

        if (range[0] > range[1])
          throw new Unsupported(`${name()} has a lower bound above its upper bound`, at)

        if (range[1] - range[0] < MAX_ENUMERATED_RANGE) {
          const values: Scalar[] = []
          for (let value = range[0]; value <= range[1]; value++) values.push(value)
          return { k: 'scalar', ty: 'int', num: true, values }
        }

        return { k: 'scalar', ty: 'int', num: true, range }
      }
    }

    if (type.isUnionType()) {
      const all = type.getTypes().map((member) => this.shapeOf(member, at, depth + 1))
      const scalars = new Map<string, Extract<Shape, { k: 'scalar' }>>()
      const alts: Shape[] = []

      for (const member of all) {
        if (member.k === 'scalar' && member.values) {
          const key = `${member.ty}:${member.num ? 1 : 0}`
          const existing = scalars.get(key)

          if (existing) existing.values = [...new Set([...existing.values!, ...member.values])]
          else {
            const copy: Extract<Shape, { k: 'scalar' }> = { ...member, values: [...member.values] }
            scalars.set(key, copy)
            alts.push(copy)
          }
        } else if (member.k === 'union') alts.push(...member.alts)
        else if (
          !alts.some(
            (a) =>
              (a.k === 'void' && member.k === 'void') || (a.k === 'null' && member.k === 'null'),
          )
        )
          alts.push(member)
      }

      return alts.length === 1 ? alts[0]! : { k: 'union', alts }
    }

    if (this.checker.isTupleType(type)) {
      const elementFlags = ((type as N).getTarget?.().elementFlags ??
        (type as N).elementFlags ??
        []) as number[]

      if (elementFlags.some((flag) => flag !== ElementFlags.Required)) {
        throw new Unsupported(
          'optional and rest tuple elements are not supported; use a union of fixed tuples such as `[A] | [A, B]`',
          at,
        )
      }

      return {
        k: 'tuple',
        items: this.checker
          .getTypeArguments(type as N)
          .map((item) => this.shapeOf(item, at, depth + 1)),
      }
    }

    if (this.checker.isArrayType(type)) {
      const [elemType] = this.checker.getTypeArguments(type as N)

      if (!elemType)
        throw new Unsupported(
          'arrays of unknown length are not supported as inputs; use a tuple',
          at,
        )

      const elemShape = this.shapeOf(elemType, at, depth + 1)

      if (elemShape.k !== 'scalar') {
        throw new Unsupported(
          'arrays of unknown length are supported for boolean, bigint, Integer and string elements; use a tuple for other element types',
          at,
        )
      }

      let range = elemShape.range

      if (!range && elemShape.ty === 'int' && elemShape.values?.length) {
        const sorted = (elemShape.values as bigint[]).toSorted((a, b) =>
          a < b ? -1 : a > b ? 1 : 0,
        )

        if (sorted.every((v, i) => i === 0 || v === sorted[i - 1]! + 1n))
          range = [sorted[0]!, sorted.at(-1)!]
        else
          throw new Unsupported(
            'arrays of non-contiguous literal unions are not supported as inputs; use a tuple',
            at,
          )
      } else if (elemShape.values && elemShape.ty !== 'bool') {
        throw new Unsupported(
          'arrays of literal unions are not supported as inputs; use a tuple',
          at,
        )
      }

      return {
        k: 'list',
        elem: elemShape.ty as ir.ScalarTy,
        ...(elemShape.num ? { num: true } : {}),
        ...(range ? { range } : {}),
      }
    }

    if (flags & TypeFlags.Object) {
      if (this.checker.getSignaturesOfType(type, SignatureKind.Call).length)
        throw new Unsupported('functions are not supported as inputs', at)

      if (this.checker.getIndexInfosOfType(type).length) {
        throw new Unsupported(
          `${name()} allows any number of properties, so its values cannot be listed; use an object type with named properties`,
          at,
        )
      }

      const fields: [string, Shape][] = []

      for (const property of this.checker.getPropertiesOfType(type)) {
        if (String(property.escapedName).startsWith('__@'))
          throw new Unsupported(
            `${name()} has a property keyed by a symbol, which is not supported in an input`,
            at,
          )

        const propertyType = this.checker.getTypeOfSymbol(property)

        if (!propertyType)
          throw new Unsupported(`the type of \`${property.name}\` could not be resolved`, at)

        const shape = this.shapeOf(propertyType, at, depth + 1)
        fields.push([
          property.name,
          property.flags & SymbolFlags.Optional
            ? {
                k: 'union',
                alts: [...(shape.k === 'union' ? shape.alts : [shape]), { k: 'absent' }],
              }
            : shape,
        ])
      }

      return { k: 'record', fields }
    }

    throw new Unsupported(`inputs of type ${name()} are not supported`, at)
  }

  private expand(shape: Shape, at: Node): Shape[] {
    const product = (parts: Shape[][]): Shape[][] =>
      parts.reduce<Shape[][]>(
        (rows, options) => {
          const next = rows.flatMap((row) => options.map((option) => [...row, option]))

          if (next.length > MAX_ALTERNATIVES)
            throw new Unsupported(
              `the input type has more than ${MAX_ALTERNATIVES} union alternatives`,
              at,
            )

          return next
        },
        [[]],
      )

    switch (shape.k) {
      case 'scalar':
      case 'list':
      case 'void':
      case 'null':
      case 'absent':
        return [shape]
      case 'union': {
        const alternatives = shape.alts.flatMap((alt) => this.expand(alt, at))

        if (alternatives.length > MAX_ALTERNATIVES)
          throw new Unsupported(
            `the input type has more than ${MAX_ALTERNATIVES} union alternatives`,
            at,
          )

        return alternatives
      }
      case 'tuple':
        return product(shape.items.map((item) => this.expand(item, at))).map((items) => ({
          k: 'tuple',
          items,
        }))
      case 'record':
        return product(shape.fields.map(([, field]) => this.expand(field, at))).map((row) => ({
          k: 'record',
          fields: row
            .map((field, i) => [shape.fields[i]![0], field] as [string, Shape])
            .filter(([, field]) => field.k !== 'absent'),
        }))
    }
  }

  private instantiate(shape: Shape, instance: LawInstance): ArgShape {
    switch (shape.k) {
      case 'scalar': {
        if (shape.values?.length === 1)
          return { k: 'const', value: shape.values[0]!, ...(shape.num ? { num: true } : {}) }

        const name = `x${instance.binders.length}`
        instance.binders.push({
          name,
          label: name,
          ty: shape.ty,
          ...(shape.values ? { domain: shape.values } : {}),
          ...(shape.num ? { num: true } : {}),
          ...(shape.range ? { range: shape.range } : {}),
        })

        if (shape.range) {
          const input = ir.variable(name, 'int')
          instance.assumptions.push(
            ir.and(ir.le(ir.lit(shape.range[0]), input), ir.le(input, ir.lit(shape.range[1]))),
          )
        }

        return { k: 'binder', name }
      }
      case 'list': {
        const name = `x${instance.binders.length}`
        const ty = ir.listTyOf(shape.elem)
        instance.binders.push({
          name,
          label: name,
          ty,
          ...(shape.num ? { num: true } : {}),
          ...(shape.range ? { range: shape.range } : {}),
        })

        if (shape.range) {
          const param = `_el${this.lambdaCounter++}`
          const v = ir.variable(param, 'int')
          instance.assumptions.push(
            ir.listAll(
              ir.variable(name, ty),
              param,
              ir.and(ir.le(ir.lit(shape.range[0]), v), ir.le(v, ir.lit(shape.range[1]))),
            ),
          )
        }

        return { k: 'binder', name }
      }
      case 'tuple':
        return { k: 'array', items: shape.items.map((item) => this.instantiate(item, instance)) }
      case 'record':
        return {
          k: 'record',
          fields: shape.fields.map(([key, field]) => [key, this.instantiate(field, instance)]),
        }
      case 'void':
        return { k: 'undefined' }
      case 'null':
        return { k: 'null' }
      case 'union':
      case 'absent':
        throw new Error('unions are expanded before instantiation')
    }
  }

  private valueOf(arg: ArgShape): Value {
    switch (arg.k) {
      case 'binder': {
        const binder = this.instance!.binders.find((b) => b.name === arg.name)!

        if (ir.isListTy(binder.ty))
          return {
            k: 'list',
            e: ir.variable(binder.name, binder.ty),
            ...(binder.num ? { num: true } : {}),
          }

        return scalar(ir.variable(binder.name, binder.ty), binder.num)
      }
      case 'const':
        return scalar(ir.lit(arg.value), arg.num)
      case 'undefined':
        return VOID
      case 'null':
        return NULL
      case 'array':
        return { k: 'array', items: arg.items.map((item) => this.valueOf(item)) }
      case 'record':
        return {
          k: 'record',
          fields: new Map(arg.fields.map(([key, field]) => [key, this.valueOf(field)])),
          unordered: true,
        }
    }
  }

  private relabel(value: Value, path: string) {
    if ((value.k === 'scalar' || value.k === 'list') && value.e.t === 'var') {
      const binder = this.instance?.binders.find(
        (b) => b.name === (value.e as { name: string }).name,
      )
      if (binder) binder.label = path
    } else if (value.k === 'record')
      for (const [key, field] of value.fields) this.relabel(field, `${path}.${key}`)
    else if (value.k === 'array')
      value.items.forEach((item, i) => this.relabel(item, `${path}[${i}]`))
  }

  private isExpect(node: N): boolean {
    return this.isCallTo(node, 'expect')
  }

  private startsWithExpect(node: N): boolean {
    let current = node

    while (current) {
      if (this.isExpect(current)) return true

      if (current.kind === K.CallExpression || current.kind === K.PropertyAccessExpression)
        current = current.expression
      else return false
    }

    return false
  }

  private expectStatement(node: N, env: Env) {
    const fail = () =>
      new Unsupported(
        'unsupported expect() matcher; use toEqual, toBe, toBeGreaterThan[OrEqual], toBeLessThan[OrEqual], toBeUndefined, toBeDefined, toBeNull, toBeTruthy, toBeFalsy, toHaveLength, toContain, toThrow, or their .not forms',
        node,
      )

    if (node.kind !== K.CallExpression || node.expression.kind !== K.PropertyAccessExpression)
      throw fail()

    const matcher = node.expression.name.text as string
    const zeroArg = [
      'toBeUndefined',
      'toBeDefined',
      'toBeNull',
      'toBeTruthy',
      'toBeFalsy',
      'toThrow',
    ].includes(matcher)
    const oneArg = [
      'toEqual',
      'toBe',
      'toBeGreaterThan',
      'toBeGreaterThanOrEqual',
      'toBeLessThan',
      'toBeLessThanOrEqual',
      'toHaveLength',
      'toContain',
    ].includes(matcher)
    if (!zeroArg && !oneArg) throw fail()
    if (node.arguments.length !== (zeroArg ? 0 : 1)) throw fail()
    let target = node.expression.expression
    let negated = false

    if (target.kind === K.PropertyAccessExpression && target.name.text === 'not') {
      negated = true
      target = target.expression
    }

    if (!this.isExpect(target) || target.arguments.length !== 1) throw fail()
    const actual = this.evalExpr(target.arguments[0], env)

    if (matcher === 'toThrow') {
      if (actual.k === 'bottom') {
        this.emit('expect', ir.FALSE, node)
        return
      }

      const checkThrow = (fn: Value): Expr => {
        if (fn.k === 'bottom') return ir.FALSE

        if (fn.k === 'choice') {
          return ir.ite(
            fn.cond,
            this.under(fn.cond, () => checkThrow(fn.a)),
            this.under(ir.not(fn.cond), () => checkThrow(fn.b)),
          )
        }

        if (fn.k !== 'closure') throw new Unsupported('toThrow expects a function', node)
        if (!this.instance) throw new Unsupported('toThrow is only supported inside a law', node)
        const THROWING = new Set<ObligationKind>([
          'unreachable',
          'nothrow',
          'undefined',
          'null',
          'tdz',
        ])
        const start = this.instance.obligations.length
        this.inThrowCheck++

        try {
          this.unchanging('a callback of `.toThrow`', node, () => this.call(fn, [], node))
        } finally {
          this.inThrowCheck--
        }

        const added = this.instance.obligations.slice(start)

        if (
          added.some((o) => o.kind === 'expect' || o.kind === 'falloff' || o.kind === 'missing')
        ) {
          throw new Unsupported(
            'a callback of `.toThrow` that calls `expect()`, falls off, or misses a key is not supported',
            node,
          )
        }

        if (added.some((o) => o.extraBinders && THROWING.has(o.kind))) {
          throw new Unsupported(
            'calling a recursive function that may throw inside `.toThrow` is not supported',
            node,
          )
        }

        const kept: Obligation[] = []
        let threw: Expr = ir.FALSE

        for (const o of added) {
          if (THROWING.has(o.kind)) threw = ir.or(threw, ir.and(o.guard, ir.not(o.claim)))
          else kept.push({ ...o, guard: ir.and(o.guard, ir.not(threw)) })
        }

        this.instance.obligations.splice(start, added.length, ...kept)
        return threw
      }

      const threw = checkThrow(actual)
      this.emit('expect', negated ? ir.not(threw) : threw, node)
      return
    }

    if (zeroArg) {
      if (actual.k === 'bottom') {
        this.emit('expect', ir.FALSE, node)
        return
      }

      let pass: Expr

      if (matcher === 'toBeUndefined') pass = this.equal(actual, VOID, node, true)
      else if (matcher === 'toBeDefined') pass = ir.not(this.equal(actual, VOID, node, true))
      else if (matcher === 'toBeNull') pass = this.equal(actual, NULL, node, true)
      else if (matcher === 'toBeTruthy') pass = this.truthy(actual, node)
      else pass = ir.not(this.truthy(actual, node))

      this.emit('expect', negated ? ir.not(pass) : pass, node)
      return
    }

    if (actual.k === 'bottom') {
      this.emit('expect', ir.FALSE, node)
      return
    }

    const expected = this.evalExpr(node.arguments[0], env)

    if (matcher === 'toEqual' || matcher === 'toBe') {
      const equal = this.equal(actual, expected, node, matcher === 'toBe')
      const sides =
        actual.k === 'scalar' && expected.k === 'scalar'
          ? { actual: actual.e, expected: expected.e, negated, num: !!actual.num }
          : undefined
      this.emit('expect', negated ? ir.not(equal) : equal, node, sides)
      return
    }

    if (expected.k === 'bottom') {
      this.emit('expect', ir.FALSE, node)
      return
    }

    if (
      matcher === 'toBeGreaterThan' ||
      matcher === 'toBeGreaterThanOrEqual' ||
      matcher === 'toBeLessThan' ||
      matcher === 'toBeLessThanOrEqual'
    ) {
      const [op, relation] = (
        {
          toBeGreaterThan: [K.GreaterThanToken, '>'],
          toBeGreaterThanOrEqual: [K.GreaterThanEqualsToken, '>='],
          toBeLessThan: [K.LessThanToken, '<'],
          toBeLessThanOrEqual: [K.LessThanEqualsToken, '<='],
        } as const
      )[matcher]
      const res = this.arithmetic(op, actual, expected, node)

      if (res.k === 'bottom') {
        this.emit('expect', ir.FALSE, node)
        return
      }

      const compared = this.scalarOf(res, node, 'bool')
      const sides =
        actual.k === 'scalar' && expected.k === 'scalar'
          ? { actual: actual.e, expected: expected.e, negated, num: !!actual.num, relation }
          : undefined
      this.emit('expect', negated ? ir.not(compared) : compared, node, sides)
      return
    }

    if (matcher === 'toHaveLength') {
      const want = this.scalarOf(expected, node.arguments[0], 'int')

      if (!isNumber(expected))
        throw new Unsupported('toHaveLength expects a number', node.arguments[0])

      const actualLen = this.over(actual, (value) => {
        if (value.k === 'bottom') return BOTTOM
        if (value.k === 'array') return scalar(ir.lit(BigInt(value.items.length)), true)
        if (value.k === 'list') return scalar(ir.listLen(value.e), true)

        if (value.k === 'scalar' && value.e.ty === 'str') {
          return scalar(ir.strLen(value.e), true)
        }

        throw new Unsupported(`toHaveLength is not supported for ${describe(value)}`, node)
      })

      if (actualLen.k === 'bottom') {
        this.emit('expect', ir.FALSE, node)
        return
      }

      const lenExpr = this.scalarOf(actualLen, node, 'int')
      const equal = ir.eq(lenExpr, want)
      this.emit('expect', negated ? ir.not(equal) : equal, node, {
        actual: lenExpr,
        expected: want,
        negated,
        num: true,
      })
      return
    }

    const has = this.over(actual, (value) => {
      if (value.k === 'bottom') return BOTTOM
      if (value.k === 'array') return this.arrayContains(value.items, expected, node)
      if (value.k === 'list') return this.listMethod(value, 'includes', [expected], node)

      if (value.k === 'scalar' && value.e.ty === 'str')
        return this.stringMethod(value.e, 'includes', [expected], node)

      throw new Unsupported(`toContain is not supported for ${describe(value)}`, node)
    })

    if (has.k === 'bottom') {
      this.emit('expect', ir.FALSE, node)
      return
    }

    const pass = this.scalarOf(has, node, 'bool')
    this.emit('expect', negated ? ir.not(pass) : pass, node)
  }

  private equal(a: Value, b: Value, at: Node, identity = false): Expr {
    if (a.k === 'bottom' || b.k === 'bottom') return ir.FALSE

    if (a.k === 'choice')
      return ir.ite(a.cond, this.equal(a.a, b, at, identity), this.equal(a.b, b, at, identity))

    if (b.k === 'choice')
      return ir.ite(b.cond, this.equal(a, b.a, at, identity), this.equal(a, b.b, at, identity))

    if (this.isPlain(a) && this.isPlain(b)) return this.strictEqual(a, b, at)

    if (
      ((a.k === 'void' || a.k === 'null') && isObject(b)) ||
      ((b.k === 'void' || b.k === 'null') && isObject(a))
    )
      return ir.FALSE

    if (identity)
      throw new Unsupported(
        'toBe compares identity, which is only modeled for booleans, bigints, numbers, strings, null and undefined; use toEqual',
        at,
      )

    if (a.k === 'list' || b.k === 'list') {
      const ref = (a.k === 'list' ? a : b) as Extract<Value, { k: 'list' }>
      const la = this.asListExpr(a, ref.e.ty as ir.ListTy, !!ref.num)
      const lb = this.asListExpr(b, ref.e.ty as ir.ListTy, !!ref.num)
      if (la && lb) return ir.eq(la.e, lb.e)
      throw new Unsupported(`cannot compare ${describe(a)} with ${describe(b)}`, at)
    }

    if (a.k === 'array' && b.k === 'array') {
      if (a.items.length !== b.items.length) return ir.FALSE
      return ir.all(a.items.map((item, i) => this.equal(item, b.items[i]!, at)))
    }

    if (a.k === 'record' && b.k === 'record') {
      if (a.fields.size !== b.fields.size || [...a.fields.keys()].some((key) => !b.fields.has(key)))
        return ir.FALSE

      return ir.all([...a.fields].map(([key, field]) => this.equal(field, b.fields.get(key)!, at)))
    }

    throw new Unsupported(`cannot compare ${describe(a)} with ${describe(b)}`, at)
  }

  private emit(kind: ObligationKind, claim: Expr, node: Node, sides?: Obligation['sides']) {
    const guard = ir.all(this.pc)
    if (guard.t === 'lit' && guard.value === false) return
    if (kind !== 'expect' && claim.t === 'lit' && claim.value === true) return

    if (!this.instance)
      throw new Unsupported('this code can throw while a module is being initialized', node)

    this.instance.obligations.push({
      kind,
      guard,
      claim,
      ...locate(node),
      text: sourceText(node),
      ...(sides ? { sides } : {}),
    })
  }

  private settle(e: Expr, refusal: () => Unsupported): Extract<Expr, { t: 'lit' }> {
    const settled = this.instance?.fixed.size ? ir.substitute(e, this.instance.fixed) : e
    if (settled.t === 'lit') return settled
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
    return {
      values: this.cells.map((cell) => cell.value),
      logged: bindingLog.length,
      scopes: scopesCreated,
      written: this.writes.length,
      frozen: this.freezes.length,
      objects: objectsCreated,
      closures: this.closuresCreated,
    }
  }

  private makeClosure(node: N, env: Env): Value {
    this.closuresCreated++
    return { k: 'closure', node, env }
  }

  private fresh<T extends Stored>(value: T): T {
    value.own = { epoch: this.epoch, born: objectsCreated++ }
    return value
  }

  private freeze(...values: Stored[]) {
    for (const value of values) {
      if (value.own && value.own.epoch !== 0) {
        this.freezes.push({ target: value, epoch: value.own.epoch })
        value.own.epoch = 0
      }
    }
  }

  private slot(target: Stored, slot: string | number): Value | undefined {
    return target.k === 'record' ? target.fields.get(slot as string) : target.items[slot as number]
  }

  private put(target: Stored, slot: string | number, value: Value | undefined) {
    if (target.k === 'record') {
      if (value === undefined) target.fields.delete(slot as string)
      else target.fields.set(slot as string, value)
    } else if (value === undefined) target.items.length = slot as number
    else target.items[slot as number] = value
  }

  private write(target: Stored, slot: string | number, value: Value) {
    this.writtenTo?.add(target)
    this.writes.push({ target, slot, previous: this.slot(target, slot) })
    this.put(target, slot, value)
  }

  private assertChangeable(target: Stored, value: Value, at: N) {
    if (target.own?.epoch !== this.epoch) {
      throw new Unsupported(
        "changing this object in place is not modeled: it is one of the law's inputs, a shared constant, or the result of a condition choosing between two objects. Copy it first, as in `{ ...value }` or `[...value]`",
        at,
      )
    }

    const seen = new Set<Value>()

    const inside = (part: Value): boolean => {
      if (part === target) return true
      if (seen.has(part)) return false
      seen.add(part)
      return part.k === 'record'
        ? [...part.fields.values()].some(inside)
        : part.k === 'array'
          ? part.items.some(inside)
          : part.k === 'choice'
            ? inside(part.a) || inside(part.b)
            : part.k === 'map' || part.k === 'set'
              ? inside(part.log)
              : false
    }

    if (inside(value)) throw new Unsupported('storing an object inside itself is not supported', at)
  }

  private changesSince(since: Saved): Changes | undefined {
    if (this.writes.length === since.written) return undefined
    const changes: Changes = new Map()

    for (let i = since.written; i < this.writes.length; i++) {
      const { target, slot } = this.writes[i]!
      if (target.own!.born >= since.objects) continue
      let slots = changes.get(target)
      if (!slots) changes.set(target, (slots = new Map()))
      slots.set(slot, this.slot(target, slot))
    }

    return changes.size ? changes : undefined
  }

  private mergeChanges(
    cond: Expr,
    whenTrue: Changes | undefined,
    whenFalse: Changes | undefined,
    dead?: 'true' | 'false',
  ) {
    if (!whenTrue && !whenFalse) return

    for (const target of new Set([...(whenTrue?.keys() ?? []), ...(whenFalse?.keys() ?? [])])) {
      const a = whenTrue?.get(target)
      const b = whenFalse?.get(target)
      const slots = [...new Set([...(a?.keys() ?? []), ...(b?.keys() ?? [])])]

      if (target.k === 'array') slots.sort((x, y) => (x as number) - (y as number))
      else if (!dead && a && b) {
        const addedA = [...a.keys()].filter(
          (k) => this.slot(target, k) === undefined && a.get(k) !== undefined,
        ) as string[]
        const addedB = [...b.keys()].filter(
          (k) => this.slot(target, k) === undefined && b.get(k) !== undefined,
        ) as string[]

        if (addedA.length > 1 && addedA.length === addedB.length) {
          const orderA = ownKeysOrdered(new Map(addedA.map((k) => [k, VOID])))
          const orderB = ownKeysOrdered(new Map(addedB.map((k) => [k, VOID])))

          if (!orderA.every((k, i) => k === orderB[i])) {
            throw new Unsupported(
              'adding properties to an object in different orders on the two sides of a condition is not supported',
              undefined,
            )
          }
        }
      }

      const deleted: (string | number)[] = []

      for (const slot of slots) {
        const now = this.slot(target, slot)
        let onTrue = a?.has(slot) ? a.get(slot) : now
        let onFalse = b?.has(slot) ? b.get(slot) : now
        if (dead === 'true') onTrue = onFalse
        if (dead === 'false') onFalse = onTrue

        if (onTrue === undefined && onFalse === undefined) {
          if (now !== undefined) deleted.push(slot)
          continue
        }

        if (onTrue === undefined || onFalse === undefined) {
          throw new Unsupported(
            target.k === 'record'
              ? 'adding or deleting a property of an object on only one side of a condition is not supported'
              : 'an array, a Map or a Set that changes length on only one side of a condition is not supported',
            undefined,
          )
        }

        const merged = this.mergeHeld(cond, onTrue, onFalse)
        if (merged !== now) this.write(target, slot, merged)
      }

      for (let i = deleted.length - 1; i >= 0; i--) {
        const slot = deleted[i]!

        if (this.slot(target, slot) !== undefined)
          this.write(target, slot, undefined as unknown as Value)
      }
    }
  }

  private unchanging<T>(what: string, at: N, run: () => T): T {
    const objects = objectsCreated
    const existing = new Set(this.cells)
    const outerAssigned = this.assignedTo
    const outerWritten = this.writtenTo
    const assigned = (this.assignedTo = new Set())
    const written = (this.writtenTo = new Set())
    let result: T

    try {
      result = run()
    } finally {
      this.assignedTo = outerAssigned
      this.writtenTo = outerWritten
      if (outerAssigned) for (const cell of assigned) outerAssigned.add(cell)
      if (outerWritten) for (const target of written) outerWritten.add(target)
    }

    for (const target of written) {
      if (target.own && target.own.born < objects)
        throw new Unsupported(
          `${what} changes an object in place, which is not modeled there; make the change in a statement of its own`,
          at,
        )
    }

    for (const cell of assigned) {
      if (existing.has(cell))
        throw new Unsupported(
          `${what} assigns to a variable outside it, which is not modeled there; make the change in a statement of its own`,
          at,
        )
    }

    return result
  }

  private restore(saved: Saved) {
    this.cells.length = saved.values.length
    this.cells.forEach((cell, i) => (cell.value = saved.values[i]!))

    while (bindingLog.length > saved.logged) {
      const entry = bindingLog.pop()!
      if (entry.env.serial < saved.scopes) entry.env.revert(entry.name, entry.previous)
    }

    while (this.writes.length > saved.written) {
      const { target, slot, previous } = this.writes.pop()!
      if (target.own!.born < saved.objects) this.put(target, slot, previous)
    }

    while (this.freezes.length > saved.frozen) {
      const { target, epoch } = this.freezes.pop()!
      if (target.own && target.own.born < saved.objects) target.own.epoch = epoch
    }
  }

  private freezesSince(since: Saved): Stored[] {
    const out: Stored[] = []

    for (let i = since.frozen; i < this.freezes.length; i++) {
      const target = this.freezes[i]!.target
      if (target.own && target.own.born < since.objects) out.push(target)
    }

    return out
  }

  private branch(
    cond: Expr,
    whenTrue: () => Value,
    whenFalse: () => Value,
    control = false,
  ): Value {
    if (cond.t === 'lit') return cond.value ? whenTrue() : whenFalse()

    if (control && this.merging > 0)
      throw new Unsupported(
        'this combination of branches and assignments is not supported',
        undefined,
      )

    const before = this.save()
    const outlives = before.values.length
    const a = this.under(cond, whenTrue)
    const changedA = this.changesSince(before)
    const frozenA = this.freezesSince(before)
    const heldA = this.cells.slice(0, outlives).map((cell) => cell.value)
    const bornA =
      a.k !== 'bottom' && this.closuresCreated > before.closures ? this.cells.slice(outlives) : []
    this.restore(before)
    const b = this.under(ir.not(cond), whenFalse)
    const changedB = this.changesSince(before)
    const frozenB = this.freezesSince(before)
    const heldB = this.cells.slice(0, outlives).map((cell) => cell.value)
    const bornB =
      b.k !== 'bottom' && this.closuresCreated > before.closures ? this.cells.slice(outlives) : []
    this.restore(before)
    this.mergeChanges(
      cond,
      changedA,
      changedB,
      a.k === 'bottom' ? 'true' : b.k === 'bottom' ? 'false' : undefined,
    )
    if (a.k !== 'bottom' && frozenA.length) this.freeze(...frozenA)
    if (b.k !== 'bottom' && frozenB.length) this.freeze(...frozenB)

    for (let i = 0; i < outlives; i++) {
      const onTrue = a.k === 'bottom' ? heldB[i]! : heldA[i]!
      const onFalse = b.k === 'bottom' ? heldA[i]! : heldB[i]!

      if (onTrue !== before.values[i] || onFalse !== before.values[i])
        this.cells[i]!.value = onTrue === onFalse ? onTrue : this.merge(cond, onTrue, onFalse)
    }

    if (bornA.length) this.cells.push(...bornA)
    if (bornB.length) this.cells.push(...bornB)
    return this.merge(cond, a, b)
  }

  private mergeStates(cond: Expr, whenTrue: () => void, whenFalse: () => void) {
    if (cond.t === 'lit') return void (cond.value ? whenTrue() : whenFalse())
    const before = this.save()
    const kept = before.values.length
    this.merging++
    let afterTrue: Value[]
    let afterFalse: Value[]
    let bornTrue: Cell[] = []
    let bornFalse: Cell[] = []
    let changedTrue: Changes | undefined
    let changedFalse: Changes | undefined
    let frozenTrue: Stored[] = []
    let frozenFalse: Stored[] = []

    try {
      this.under(cond, whenTrue)
      afterTrue = this.cells.slice(0, kept).map((cell) => cell.value)
      if (this.closuresCreated > before.closures) bornTrue = this.cells.slice(kept)
      changedTrue = this.changesSince(before)
      frozenTrue = this.freezesSince(before)
      this.restore(before)
      this.under(ir.not(cond), whenFalse)
      afterFalse = this.cells.slice(0, kept).map((cell) => cell.value)
      if (this.closuresCreated > before.closures) bornFalse = this.cells.slice(kept)
      changedFalse = this.changesSince(before)
      frozenFalse = this.freezesSince(before)
      this.restore(before)
    } finally {
      this.merging--
    }

    this.mergeChanges(cond, changedTrue, changedFalse)
    if (frozenTrue.length) this.freeze(...frozenTrue)
    if (frozenFalse.length) this.freeze(...frozenFalse)
    this.cells.forEach((cell, i) => {
      const a = afterTrue[i]!
      const b = afterFalse[i]!
      cell.value = a === b ? a : this.merge(cond, a, b)
    })
    if (bornTrue.length) this.cells.push(...bornTrue)
    if (bornFalse.length) this.cells.push(...bornFalse)
  }

  private mergeHeld(cond: Expr, a: Value, b: Value): Value {
    if (a === b) return a
    if (a.k === 'bottom') return b
    if (b.k === 'bottom') return a

    if (a.k === 'scalar' && b.k === 'scalar' && a.e.ty === b.e.ty && !!a.num === !!b.num)
      return scalar(ir.ite(cond, a.e, b.e), a.num)

    if (a.k === 'list' && b.k === 'list' && a.e.ty === b.e.ty && !!a.num === !!b.num)
      return { k: 'list', e: ir.ite(cond, a.e, b.e), ...(a.num ? { num: true } : {}) }

    if (a.k === 'rat' && b.k === 'rat' && a.shift === b.shift)
      return { k: 'rat', num: ir.ite(cond, a.num, b.num), shift: a.shift }

    if (a.k === 'float' && b.k === 'float' && a.value === b.value) return a
    if (a.k === 'closure' && b.k === 'closure' && a.node === b.node && a.env === b.env) return a
    if (a.k === 'void' && b.k === 'void') return a
    if (a.k === 'null' && b.k === 'null') return a
    return { k: 'choice', cond, a, b }
  }

  private merge(cond: Expr, a: Value, b: Value): Value {
    if (a === b) return a
    if (a.k === 'bottom') return b
    if (b.k === 'bottom') return a

    if (a.k === 'scalar' && b.k === 'scalar' && a.e.ty === b.e.ty && !!a.num === !!b.num)
      return scalar(ir.ite(cond, a.e, b.e), a.num)

    if (a.k === 'list' && b.k === 'list' && a.e.ty === b.e.ty && !!a.num === !!b.num)
      return { k: 'list', e: ir.ite(cond, a.e, b.e), ...(a.num ? { num: true } : {}) }

    if (a.k === 'rat' && b.k === 'rat' && a.shift === b.shift)
      return { k: 'rat', num: ir.ite(cond, a.num, b.num), shift: a.shift }

    if (a.k === 'float' && b.k === 'float' && a.value === b.value) return a

    if (a.k === 'array' && b.k === 'array' && a.items.length === b.items.length) {
      this.freeze(a, b)
      return { k: 'array', items: a.items.map((item, i) => this.merge(cond, item, b.items[i]!)) }
    }

    if (
      a.k === 'record' &&
      b.k === 'record' &&
      a.fields.size === b.fields.size &&
      [...a.fields.keys()].every((key) => b.fields.has(key))
    ) {
      const orderA = ownKeysOrdered(a.fields)
      const orderB = ownKeysOrdered(b.fields)
      if (!orderA.every((key, i) => key === orderB[i])) return { k: 'choice', cond, a, b }
      this.freeze(a, b)
      return {
        k: 'record',
        fields: new Map(
          [...a.fields].map(([key, field]) => [key, this.merge(cond, field, b.fields.get(key)!)]),
        ),
        ...(a.unordered || b.unordered ? { unordered: true } : {}),
      }
    }

    if (a.k === 'closure' && b.k === 'closure' && a.node === b.node && a.env === b.env) return a
    if (a.k === 'void' && b.k === 'void') return a
    if (a.k === 'null' && b.k === 'null') return a
    return { k: 'choice', cond, a, b }
  }

  private over(value: Value, apply: (value: Value) => Value): Value {
    value = this.settled(value)

    if (value.k === 'choice')
      return this.branch(
        value.cond,
        () => this.over(value.a, apply),
        () => this.over(value.b, apply),
      )

    return apply(value)
  }

  private factsOf(fn: N) {
    let facts = this.facts.get(fn)
    if (facts) return facts
    facts = {
      assigned: new Set<string>(),
      mentioned: new Set<string>(),
      returnsValue: false,
      usesVar: undefined,
      isRecursive: false,
    }
    const selfName: string | undefined = fn.name?.kind === K.Identifier ? fn.name.text : undefined

    const isFunction = (node: N) =>
      node.kind === K.ArrowFunction ||
      node.kind === K.FunctionExpression ||
      node.kind === K.FunctionDeclaration

    const shadowsSelf = (statements: readonly N[]): boolean => {
      if (!selfName) return false

      for (const stmt of statements) {
        if (
          stmt.kind === K.FunctionDeclaration &&
          stmt.name?.kind === K.Identifier &&
          stmt.name.text === selfName
        )
          return true

        if (stmt.kind === K.VariableStatement) {
          const names = new Set<string>()

          for (const decl of stmt.declarationList.declarations as N[])
            collectNames(decl.name, names)

          if (names.has(selfName)) return true
        }
      }

      return false
    }

    const visit = (node: N, nested: boolean, shadowed: boolean) => {
      if (node.kind === K.Identifier) facts!.mentioned.add(node.text)

      if (
        !shadowed &&
        selfName &&
        node.kind === K.CallExpression &&
        node.expression.kind === K.Identifier &&
        node.expression.text === selfName
      ) {
        facts!.isRecursive = true
      }

      if (
        node.kind === K.BinaryExpression &&
        node.operatorToken.kind >= K.FirstAssignment &&
        node.operatorToken.kind <= K.LastAssignment
      ) {
        collectNames(node.left, facts!.assigned)
      }

      if (
        (node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
        (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)
      )
        collectNames(node.operand, facts!.assigned)

      if (node.kind === K.ReturnStatement && node.expression && !nested) facts!.returnsValue = true

      if (
        node.kind === K.VariableDeclarationList &&
        !(node.flags & (NodeFlags.Let | NodeFlags.Const)) &&
        !nested
      )
        facts!.usesVar ??= node

      const nextShadowed = shadowed || (node.kind === K.Block && shadowsSelf(node.statements))
      node.forEachChild((child: N) => {
        let childShadowed = nextShadowed

        if (!childShadowed && selfName && isFunction(child)) {
          if (child.name?.kind === K.Identifier && child.name.text === selfName)
            childShadowed = true
          else {
            const pNames = new Set<string>()
            for (const p of parametersOf(child)) collectNames(p.name, pNames)
            if (pNames.has(selfName)) childShadowed = true
          }
        }

        visit(child, nested || isFunction(child), childShadowed)
      })
    }

    const paramNames = new Set<string>()

    for (const parameter of parametersOf(fn)) {
      collectNames(parameter.name, paramNames)
      visit(parameter, false, false)
    }

    if (fn.body) visit(fn.body, false, selfName !== undefined && paramNames.has(selfName))
    this.facts.set(fn, facts)
    return facts
  }

  private declare(statement: N, env: Env) {
    const list = statement.declarationList ?? statement
    const reassignable = (list.flags & NodeFlags.Let) !== 0

    if (!reassignable && !(list.flags & NodeFlags.Const))
      throw new Unsupported('`var` is not supported; use `const` or `let`', statement)

    for (const declaration of list.declarations as N[]) {
      if (!declaration.initializer && !reassignable)
        throw new Unsupported('a declaration needs an initializer', declaration)

      this.bind(
        declaration.name,
        declaration.initializer ? this.evalExpr(declaration.initializer, env) : VOID,
        env,
        false,
        reassignable,
      )
    }
  }

  private bind(pattern: N, value: Value, env: Env, label = false, reassignable = false) {
    if (pattern.kind === K.Identifier) {
      const cell = env.set(
        pattern.text,
        value,
        reassignable && this.assigned.at(-1)?.has(pattern.text) === true,
      )
      if (cell.mutable) this.cells.push(cell)
      if (label) this.relabel(value, pattern.text)
      return
    }

    if (pattern.kind === K.ArrayBindingPattern) {
      const part = (read: (array: Extract<Value, { k: 'array' }>) => Value) =>
        this.over(value, (whole) => {
          if (whole.k === 'bottom') return BOTTOM

          if (whole.k !== 'array')
            throw new Unsupported(`cannot destructure ${describe(whole)} as an array`, pattern)

          return read(whole)
        })

      const lists = new Set<Value>()

      const collect = (whole: Value): void => {
        if (whole.k === 'choice') {
          collect(whole.a)
          collect(whole.b)
        } else lists.add(whole)
      }

      collect(value)
      const written = this.writes.length

      const unchanged = (at: N) => {
        for (let w = written; w < this.writes.length; w++) {
          if (lists.has(this.writes[w]!.target))
            throw new Unsupported(
              'a default in a pattern that changes the list being taken apart is not supported',
              at,
            )
        }
      }
      ;(pattern.elements as N[]).forEach((element, i) => {
        unchanged(element)
        if (element.kind === K.OmittedExpression || !element.name) return

        if (element.dotDotDotToken)
          return this.bind(
            element.name,
            part((array) => this.fresh({ k: 'array', items: array.items.slice(i) })),
            env,
            label,
            reassignable,
          )

        const item = part((array) => array.items[i] ?? this.absent(undefined, element))
        this.bind(
          element.name,
          element.initializer ? this.defaulted(item, element.initializer, env) : item,
          env,
          label,
          reassignable,
        )
      })
      return
    }

    if (pattern.kind === K.ObjectBindingPattern) {
      const part = (read: (record: Extract<Value, { k: 'record' }>) => Value) =>
        this.over(value, (whole) => {
          if (whole.k === 'bottom') return BOTTOM

          if (whole.k !== 'record')
            throw new Unsupported(`cannot destructure ${describe(whole)} as an object`, pattern)

          return read(whole)
        })

      const taken = new Set<string>()

      for (const element of pattern.elements as N[]) {
        if (element.dotDotDotToken) {
          const named = new Set(taken)
          this.bind(
            element.name,
            part((record) =>
              this.fresh({
                k: 'record',
                fields: new Map([...record.fields].filter(([name]) => !named.has(name))),
                ...(record.unordered ? { unordered: true } : {}),
              }),
            ),
            env,
            label,
            reassignable,
          )
          continue
        }

        const key = element.propertyName ?? element.name

        if (key.kind !== K.Identifier && key.kind !== K.StringLiteral)
          throw new Unsupported('computed property names are not supported', element)

        taken.add(key.text)
        const field = part(
          (record) => record.fields.get(key.text) ?? this.absent(key.text, element),
        )
        this.bind(
          element.name,
          element.initializer ? this.defaulted(field, element.initializer, env) : field,
          env,
          label,
          reassignable,
        )
      }

      return
    }

    throw new Unsupported('this binding pattern is not supported', pattern)
  }

  private valueFromExpr(e: Expr, num?: boolean): Value {
    if (ir.isListTy(e.ty)) return { k: 'list', e, ...(num ? { num: true } : {}) }
    return scalar(e, num)
  }

  private asListExpr(
    value: Value,
    wantTy?: ir.ListTy,
    wantNum?: boolean,
  ): { e: Expr; num?: boolean } | undefined {
    value = this.settled(value)

    if (value.k === 'list') {
      if (wantTy && value.e.ty !== wantTy) return undefined
      if (wantNum !== undefined && !!value.num !== wantNum) return undefined
      return { e: value.e, ...(value.num ? { num: true } : {}) }
    }

    if (value.k === 'array') {
      if (value.items.length === 0) {
        return wantTy ? { e: ir.listLit(wantTy, []), ...(wantNum ? { num: true } : {}) } : undefined
      }

      const first = this.settled(value.items[0]!)
      if (first.k !== 'scalar') return undefined
      const elemTy = first.e.ty as ir.ScalarTy
      const listTy = ir.listTyOf(elemTy)
      const num = !!first.num
      if (wantTy && listTy !== wantTy) return undefined
      if (wantNum !== undefined && num !== wantNum) return undefined
      const exprs: Expr[] = []

      for (const raw of value.items) {
        const item = this.settled(raw)
        if (item.k !== 'scalar' || item.e.ty !== elemTy || !!item.num !== num) return undefined
        exprs.push(item.e)
      }

      return { e: ir.listLit(listTy, exprs), ...(num ? { num: true } : {}) }
    }

    return undefined
  }

  private irArgOf(
    value: Value,
    expectedTy?: Ty,
    expectedNum?: boolean,
  ): { e: Expr; ty: Ty; num?: boolean } | undefined {
    value = this.settled(value)

    if (value.k === 'scalar') {
      if (expectedTy && value.e.ty !== expectedTy) return undefined
      if (expectedNum !== undefined && !!value.num !== expectedNum) return undefined
      return { e: value.e, ty: value.e.ty, ...(value.num ? { num: true } : {}) }
    }

    if (value.k === 'list' || value.k === 'array') {
      const list = this.asListExpr(
        value,
        expectedTy && ir.isListTy(expectedTy) ? expectedTy : undefined,
        expectedNum,
      )
      if (!list) return undefined
      if (expectedTy && list.e.ty !== expectedTy) return undefined
      return { e: list.e, ty: list.e.ty, ...(list.num ? { num: true } : {}) }
    }

    return undefined
  }

  private returnIrType(node: N): { ty: Ty; num?: boolean } | undefined {
    const type = node.type
      ? this.checker.getTypeFromTypeNode(node.type)
      : (() => {
          const sig = this.checker.getSignatureFromDeclaration?.(node)
          return sig ? this.checker.getReturnTypeOfSignature?.(sig) : undefined
        })()
    if (!type) return undefined
    if (type.flags & (TypeFlags.Boolean | TypeFlags.BooleanLiteral)) return { ty: 'bool' }
    if (type.flags & (TypeFlags.BigInt | TypeFlags.BigIntLiteral)) return { ty: 'int' }
    if (type.flags & (TypeFlags.String | TypeFlags.StringLiteral)) return { ty: 'str' }
    if (type.flags & (TypeFlags.Number | TypeFlags.NumberLiteral)) return { ty: 'int', num: true }

    if (this.checker.isArrayType(type)) {
      const [elem] = this.checker.getTypeArguments(type as N)
      if (!elem) return undefined
      if (elem.flags & (TypeFlags.Boolean | TypeFlags.BooleanLiteral)) return { ty: 'list_bool' }
      if (elem.flags & (TypeFlags.BigInt | TypeFlags.BigIntLiteral)) return { ty: 'list_int' }
      if (elem.flags & (TypeFlags.String | TypeFlags.StringLiteral)) return { ty: 'list_str' }

      if (elem.flags & (TypeFlags.Number | TypeFlags.NumberLiteral))
        return { ty: 'list_int', num: true }
    }

    return undefined
  }

  private safeLeanDefName(raw: string): string {
    const reserved = new Set([
      'def',
      'theorem',
      'lemma',
      'axiom',
      'example',
      'let',
      'in',
      'if',
      'then',
      'else',
      'match',
      'with',
      'fun',
      'by',
      'do',
      'for',
      'return',
      'where',
      'import',
      'prelude',
      'true',
      'false',
      'Nat',
      'Int',
      'Bool',
      'String',
      'List',
    ])
    const base =
      /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(raw) &&
      !reserved.has(raw) &&
      !/^(?:c\d+|x\d+|_p_|_v\d+|_el\d+|_acc\d+)/.test(raw)
        ? raw
        : `_fn_${raw.replace(/[^a-zA-Z0-9_]/g, '_')}`
    const used = new Set((this.instance?.defs ?? []).map((d) => d.name))
    if (!used.has(base)) return base
    let k = 1
    while (used.has(`${base}_${k}`)) k++
    return `${base}_${k}`
  }

  private callRecursive(
    fn: Extract<Value, { k: 'closure' }>,
    args: Value[],
    at: N,
  ): Value | undefined {
    const node = fn.node
    const active = this.compilingFns.get(node)

    if (active) {
      if (args.length !== active.params.length)
        throw new Unsupported('recursive call argument count does not match its parameters', at)

      const argExprs = active.params.map((p, i) => {
        const converted = this.irArgOf(args[i]!, p.ty, !!p.num)

        if (!converted)
          throw new Unsupported(`recursive call argument ${i + 1} has an incompatible type`, at)

        return converted.e
      })
      active.calls.push(argExprs)
      return this.valueFromExpr(ir.callFn(active.name, active.retTy, argExprs), active.retNum)
    }

    if (!this.instance) return undefined
    const parameters = parametersOf(node)
    if (parameters.length === 0 || parameters.length !== args.length) return undefined

    if (parameters.some((p) => p.name.kind !== K.Identifier || p.dotDotDotToken || p.initializer))
      return undefined

    const facts = this.factsOf(node)
    const paramNames = new Set(parameters.map((p) => p.name.text as string))

    for (const name of facts.mentioned) {
      if (paramNames.has(name)) continue
      const cell = fn.env.cell(name)
      if (cell && cell.value !== fn) return undefined
    }

    const convertedArgs: { e: Expr; ty: Ty; num?: boolean }[] = []

    for (const arg of args) {
      const irArg = this.irArgOf(arg)
      if (!irArg) return undefined
      convertedArgs.push(irArg)
    }

    let nodeId = this.fnNodeIds.get(node)
    if (nodeId === undefined) this.fnNodeIds.set(node, (nodeId = this.nextFnNodeId++))
    const sigKey = `${nodeId}:${convertedArgs.map((a) => `${a.ty}:${a.num ? 1 : 0}`).join(',')}`
    const cached = this.compiledFns.get(sigKey)

    if (cached)
      return this.valueFromExpr(
        ir.callFn(
          cached.name,
          cached.retTy,
          convertedArgs.map((a) => a.e),
        ),
        cached.retNum,
      )

    const ret = this.returnIrType(node)
    if (!ret) return undefined
    const rawName = node.name?.kind === K.Identifier ? (node.name.text as string) : 'rec'
    const defName = this.safeLeanDefName(rawName)
    const params = parameters.map((p, i) => ({
      name: `_p${i}`,
      orig: p.name.text as string,
      ty: convertedArgs[i]!.ty,
      ...(convertedArgs[i]!.num ? { num: true } : {}),
    }))
    const info = {
      name: defName,
      params: params.map(({ name, ty, num }) => ({ name, ty, ...(num ? { num } : {}) })),
      retTy: ret.ty,
      ...(ret.num ? { retNum: true } : {}),
      calls: [] as Expr[][],
    }

    if (facts.usesVar)
      throw new Unsupported('`var` is not supported; use `const` or `let`', facts.usesVar)

    this.noteExpectations(node)
    const savedPc = this.pc
    const savedFrame = this.frame
    const savedMerging = this.merging
    const live = this.cells.length
    const startObs = this.instance.obligations.length
    this.compilingFns.set(node, info)
    this.pc = []
    this.frame = live
    this.merging = 0
    this.assigned.push(facts.assigned)
    let bodyVal: Value

    try {
      bodyVal = this.unchanging(`the recursive function \`${rawName}\``, at, () => {
        const env = fn.env.child()
        if (node.kind === K.FunctionExpression && node.name) env.set(node.name.text, fn)
        params.forEach((p) => {
          const cell = env.set(
            p.orig,
            this.valueFromExpr(ir.variable(p.name, p.ty), p.num),
            facts.assigned.has(p.orig),
          )
          if (cell.mutable) this.cells.push(cell)
        })
        if (node.body.kind !== K.Block) return this.evalExpr(node.body, env)
        return this.block(node.body.statements, env.child(), {
          next: () => {
            if (!facts.returnsValue) return VOID
            this.emit('falloff', ir.FALSE, node)
            return BOTTOM
          },
        })
      })
    } finally {
      this.compilingFns.delete(node)
      this.assigned.pop()
      this.cells.length = live
      this.pc = savedPc
      this.frame = savedFrame
      this.merging = savedMerging
    }

    if (!info.calls.length) {
      this.instance.obligations.length = startObs
      return undefined
    }

    const bodyExpr = this.irArgOf(bodyVal, ret.ty, !!ret.num)

    if (!bodyExpr)
      throw new Unsupported(
        `recursive function \`${rawName}\` must return a consistent boolean, bigint, number, string or array`,
        node,
      )

    const allowedParams = new Set(params.map((p) => p.name))

    for (const v of ir.freeVariables(bodyExpr.e)) {
      if (!allowedParams.has(v)) {
        this.instance.obligations.length = startObs
        return undefined
      }
    }

    const addedObs = this.instance.obligations.slice(startObs)

    if (addedObs.some((o) => o.kind === 'expect')) {
      throw new Unsupported(
        `recursive function \`${rawName}\` containing \`expect()\` is not supported`,
        node,
      )
    }

    for (const o of addedObs) {
      for (const v of [...ir.freeVariables(o.guard), ...ir.freeVariables(o.claim)]) {
        if (!allowedParams.has(v)) {
          this.instance.obligations.length = startObs
          return undefined
        }
      }
    }

    const extraBinders: Binder[] = params.map((p) => ({
      name: p.name,
      label: `${rawName}(${p.orig})`,
      ty: p.ty,
      ...(p.num ? { num: true } : {}),
    }))
    for (const o of addedObs) o.extraBinders = extraBinders
    const changing = params.filter((p, idx) =>
      info.calls.some((c) => !ir.same(c[idx]!, ir.variable(p.name, p.ty))),
    )
    const changingLists = changing.filter((p) => ir.isListTy(p.ty))
    const changingInts = changing.filter((p) => p.ty === 'int')
    let measure: string

    if (changingLists.length) {
      measure = changingLists.map((p) => `${p.name}.length`).join(' + ')
    } else if (changingInts.length === 1) {
      const p = changingInts[0]!
      const pIdx = params.indexOf(p)
      const fixedInt = params.find((q) => q !== p && q.ty === 'int' && !changing.includes(q))
      const increases = info.calls.every((c) => {
        const arg = c[pIdx]!
        return (
          arg.t === 'op' &&
          arg.op === 'add' &&
          ir.same(arg.args[0]!, ir.variable(p.name, 'int')) &&
          arg.args[1]!.t === 'lit' &&
          (arg.args[1]!.value as bigint) > 0n
        )
      })
      measure = increases && fixedInt ? `(${fixedInt.name} - ${p.name}).toNat` : `${p.name}.natAbs`
    } else if (changingInts.length > 1) {
      measure = changingInts.map((p) => `${p.name}.natAbs`).join(' + ')
    } else {
      const firstList = params.find((p) => ir.isListTy(p.ty))
      const firstInt = params.find((p) => p.ty === 'int')

      if (!firstList && !firstInt) {
        this.instance.obligations.length = startObs
        return undefined
      }

      measure = firstList ? `${firstList.name}.length` : `${firstInt!.name}.natAbs`
    }

    const def: ir.FnDef = {
      name: defName,
      params: info.params,
      retTy: ret.ty,
      ...(ret.num ? { retNum: true } : {}),
      body: bodyExpr.e,
      measure,
    }
    this.instance.defs ??= []
    this.instance.defs.push(def)
    this.compiledFns.set(sigKey, def)
    return this.valueFromExpr(
      ir.callFn(
        def.name,
        def.retTy,
        convertedArgs.map((a) => a.e),
      ),
      def.retNum,
    )
  }

  private call(fn: Value, args: Value[], at: N): Value {
    if (fn.k === 'choice')
      return this.branch(
        fn.cond,
        () => this.call(fn.a, args, at),
        () => this.call(fn.b, args, at),
      )

    if (fn.k === 'void') return this.throwsOnUndefined(at)
    if (fn.k === 'null') return this.throwsOnNull(at)
    if (fn.k !== 'closure') throw new Unsupported(`cannot call ${describe(fn)}`, at)
    const node = fn.node

    if (node.asteriskToken || node.modifiers?.some((m: N) => m.kind === K.AsyncKeyword))
      throw new Unsupported('async functions and generators are not supported', at)

    if (!node.body) throw new Unsupported('this function has no body to translate', at)
    const facts = this.factsOf(node)

    if (this.compilingFns.has(node) || (facts.isRecursive && !this.stack.includes(node))) {
      const rec = this.callRecursive(fn, args, at)
      if (rec) return rec
    }

    if (this.stack.includes(node))
      throw new Unsupported('recursive functions are not supported', at)

    if (facts.usesVar)
      throw new Unsupported('`var` is not supported; use `const` or `let`', facts.usesVar)

    this.noteExpectations(node)
    const env = fn.env.child()
    const live = this.cells.length
    const beforeClosures = this.closuresCreated
    const frame = this.frame
    this.frame = live
    const merging = this.merging
    this.merging = 0
    this.stack.push(node)
    this.assigned.push(facts.assigned)

    try {
      if (node.kind === K.FunctionExpression && node.name) env.set(node.name.text, fn)
      const parameters = parametersOf(node)

      for (const parameter of parameters)
        for (const name of boundNames(parameter.name)) env.set(name, UNINITIALIZED)

      parameters.forEach((parameter, i) => {
        if (parameter.dotDotDotToken) {
          this.bind(
            parameter.name,
            this.fresh({ k: 'array', items: args.slice(i) }),
            env,
            false,
            true,
          )
          return
        }

        const value = args[i] ?? VOID
        this.bind(
          parameter.name,
          parameter.initializer ? this.defaulted(value, parameter.initializer, env) : value,
          env,
          false,
          true,
        )
      })
      if (node.body.kind !== K.Block) return this.evalExpr(node.body, env)
      return this.block(node.body.statements, env.child(), {
        next: () => {
          if (!facts.returnsValue) return VOID
          this.emit('falloff', ir.FALSE, node)
          return BOTTOM
        },
      })
    } finally {
      this.stack.pop()
      this.assigned.pop()
      if (this.closuresCreated === beforeClosures) this.cells.length = live
      this.frame = frame
      this.merging = merging
    }
  }

  private block(statements: readonly N[], scope: Env, flow: Flow): Value {
    this.enter(statements, scope)
    return this.exec(statements, 0, scope, flow)
  }

  private enter(statements: readonly N[], scope: Env) {
    for (const statement of statements) {
      if (statement.kind === K.FunctionDeclaration && statement.name)
        scope.set(statement.name.text, this.makeClosure(statement, scope))
      else if (statement.kind === K.VariableStatement) {
        for (const declaration of statement.declarationList.declarations as N[]) {
          for (const name of boundNames(declaration.name)) scope.set(name, UNINITIALIZED)
        }
      } else if (statement.kind === K.ClassDeclaration && statement.name)
        scope.set(statement.name.text, UNINITIALIZED)
    }
  }

  private exec(statements: readonly N[], i: number, env: Env, flow: Flow): Value {
    if (i >= statements.length) return flow.next()
    const statement = statements[i]

    if (++this.steps > MAX_STEPS)
      throw new Unsupported('this code has too many paths to follow', statement)

    const rest = () => this.exec(statements, i + 1, env, flow)
    const after: Flow = { ...flow, next: rest }

    const run = (block: N | undefined, to: Flow): Value =>
      block
        ? this.block(block.kind === K.Block ? block.statements : [block], env.child(), to)
        : to.next()

    switch (statement.kind) {
      case K.EmptyStatement:
        return rest()
      case K.VariableStatement:
        this.declare(statement, env)
        return rest()
      case K.FunctionDeclaration:
        return rest()
      case K.ExpressionStatement:
        this.effect(statement.expression, env)
        return rest()
      case K.ReturnStatement:
        return statement.expression ? this.evalExpr(statement.expression, env) : VOID
      case K.ThrowStatement: {
        if (this.inThrowCheck > 0 && statement.expression) {
          const expr = statement.expression

          if (
            (expr.kind === K.NewExpression || expr.kind === K.CallExpression) &&
            expr.expression.kind === K.Identifier &&
            [
              'Error',
              'TypeError',
              'RangeError',
              'ReferenceError',
              'SyntaxError',
              'URIError',
              'EvalError',
            ].includes(expr.expression.text) &&
            !env.get(expr.expression.text) &&
            this.isBuiltin(expr.expression)
          ) {
            this.assertBuiltinsIntact(expr)
            this.arguments({ arguments: expr.arguments ?? [] }, env)
          } else {
            this.evalExpr(expr, env)
          }
        }

        this.emit('unreachable', ir.FALSE, statement)
        return BOTTOM
      }
      case K.BreakStatement:
      case K.ContinueStatement: {
        const target = statement.kind === K.BreakStatement ? flow.brk : flow.cont

        if (statement.label || !target)
          throw new Unsupported('this break or continue is not supported', statement)

        return target()
      }
      case K.Block:
        return run(statement, after)
      case K.IfStatement: {
        const condVal = this.evalExpr(statement.expression, env)
        if (condVal.k === 'bottom') return BOTTOM
        const cond = this.truthy(condVal, statement.expression)

        if (cond.t === 'lit')
          return run(cond.value ? statement.thenStatement : statement.elseStatement, after)

        if (canExit(statement.thenStatement) || canExit(statement.elseStatement)) {
          return this.branch(
            cond,
            () => run(statement.thenStatement, after),
            () => run(statement.elseStatement, after),
            true,
          )
        }

        const stop: Flow = { next: () => VOID }
        this.mergeStates(
          cond,
          () => run(statement.thenStatement, stop),
          () => run(statement.elseStatement, stop),
        )
        return rest()
      }
      case K.SwitchStatement: {
        const subject = this.evalExpr(statement.expression, env)
        if (subject.k === 'bottom') return BOTTOM
        const clauses = statement.caseBlock.clauses as N[]
        const scope = env.child()
        this.enter(
          clauses.flatMap((clause) => clause.statements as N[]),
          scope,
        )

        const statementsFrom = (start: number) =>
          clauses.slice(start).flatMap((clause) => clause.statements as N[])

        const matchesAt = (clause: N): Expr | undefined => {
          const label = this.evalExpr(clause.expression, scope)
          const eq = this.eqValues(subject, label, clause)
          return eq.k === 'bottom' ? undefined : this.scalarOf(eq, clause, 'bool')
        }

        for (const [index, clause] of clauses.entries()) {
          if (clause.kind === K.DefaultClause && index !== clauses.length - 1)
            throw new Unsupported('`default` must be the last clause of a switch', clause)
        }

        if (!canExit(statement)) {
          const stop: Flow = { next: () => VOID }

          const settle = (index: number): void => {
            const clause = clauses[index]
            if (!clause) return

            if (clause.kind === K.DefaultClause)
              return void this.exec(statementsFrom(index), 0, scope, stop)

            const matched = matchesAt(clause)
            if (!matched) return
            this.mergeStates(
              matched,
              () => void this.exec(statementsFrom(index), 0, scope, stop),
              () => settle(index + 1),
            )
          }

          settle(0)
          return rest()
        }

        const bodyFrom = (start: number) =>
          this.exec(statementsFrom(start), 0, scope, { ...flow, next: rest, brk: rest })

        const from = (index: number): Value => {
          const clause = clauses[index]
          if (!clause) return rest()
          if (clause.kind === K.DefaultClause) return bodyFrom(index)
          const matched = matchesAt(clause)
          if (!matched) return BOTTOM
          return this.branch(
            matched,
            () => bodyFrom(index),
            () => from(index + 1),
            true,
          )
        }

        return from(0)
      }
      case K.ForOfStatement: {
        const declarations = statement.initializer
        const declared =
          declarations.kind === K.VariableDeclarationList ? (declarations.declarations as N[]) : []
        const reassignable = (declarations.flags & NodeFlags.Let) !== 0

        if (
          statement.awaitModifier ||
          declared.length !== 1 ||
          declared[0].initializer ||
          (!reassignable && !(declarations.flags & NodeFlags.Const))
        ) {
          throw new Unsupported('a loop must be written `for (const item of items)`', statement)
        }

        const header = env.child()
        for (const name of boundNames(declared[0].name)) header.set(name, UNINITIALIZED)
        const body = statement.statement

        const loop = (source: Value, after: () => Value): Value => {
          if (source.k === 'bottom') return BOTTOM

          if (source.k === 'iterator' && canExit(body)) {
            throw new Unsupported(
              'leaving a loop over a Map or Set iterator early is not supported',
              statement,
            )
          }

          const items = this.listed(source, statement.expression)

          if (items.k === 'list') {
            this.foldListForOf(items, declared[0].name, reassignable, body, env, statement)
            return after()
          }

          if (items.k !== 'array')
            throw new Unsupported(
              `a loop needs an array whose length is known here, but this is ${describe(items)}`,
              statement.expression,
            )

          const activeIter = source.k === 'iterator' ? source.state : undefined
          const collection =
            source.k === 'iterator'
              ? source.source
              : source.k === 'map' || source.k === 'set'
                ? source
                : undefined
          const entered = collection ? collection.log.items.length : undefined

          const doneLoop = () => {
            if (activeIter) this.activeIterators.delete(activeIter)
            return after()
          }

          const iterate = (index: number): Value => {
            if (entered !== undefined && collection!.log.items.length !== entered) {
              throw new Unsupported(
                'changing a Map or a Set inside a loop over it is not supported',
                statement,
              )
            }

            const item = items.items[index]
            if (!item) return doneLoop()
            const scope = env.child()
            for (const bound of boundNames(declared[0].name)) scope.set(bound, UNINITIALIZED)
            this.bind(declared[0].name, item, scope, false, reassignable)
            const onward = () => iterate(index + 1)
            return this.block(body.kind === K.Block ? body.statements : [body], scope.child(), {
              next: onward,
              cont: onward,
              brk: doneLoop,
            })
          }

          if (activeIter) this.activeIterators.add(activeIter)

          try {
            return iterate(0)
          } finally {
            if (activeIter) this.activeIterators.delete(activeIter)
          }
        }

        const run = (items: Value): Value => {
          items = this.settled(items)
          if (items.k !== 'choice') return loop(items, rest)
          const choice = items

          if (canExit(body))
            return this.branch(
              choice.cond,
              () => run(choice.a),
              () => run(choice.b),
              true,
            )

          const each = (list: Value): void => {
            list = this.settled(list)

            if (list.k === 'choice') {
              const inner = list
              this.mergeStates(
                inner.cond,
                () => each(inner.a),
                () => each(inner.b),
              )
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
        const scope = env.child()
        const initializer = statement.kind === K.ForStatement ? statement.initializer : undefined
        const letNames =
          statement.kind === K.ForStatement &&
          initializer?.kind === K.VariableDeclarationList &&
          initializer.flags & NodeFlags.Let
            ? (initializer.declarations as N[]).flatMap((declaration) =>
                boundNames(declaration.name),
              )
            : []

        if (initializer?.kind === K.VariableDeclarationList) {
          for (const declaration of initializer.declarations as N[])
            for (const name of boundNames(declaration.name)) scope.set(name, UNINITIALIZED)

          this.declare(initializer, scope)
        } else if (initializer) this.effect(initializer, scope)

        const perIteration = (prev: Env): Env => {
          if (!letNames.length) return prev
          const next = env.child()

          for (const name of letNames) {
            const old = prev.cell(name)!
            const cell = next.set(name, old.value, old.mutable)
            if (cell.mutable) this.cells.push(cell)
          }

          return next
        }

        const firstEnv = perIteration(scope)
        const condition =
          statement.kind === K.ForStatement ? statement.condition : statement.expression
        const body = statement.statement
        let rounds = 0

        if (!canExit(body)) {
          const stop: Flow = { next: () => VOID }
          let cur = firstEnv

          const check = () => {
            const cond = condition ? this.bool(condition, cur) : ir.TRUE
            return this.settle(
              cond,
              () =>
                new Unsupported(
                  'how many times this loop runs depends on a value that is not known here',
                  condition,
                ),
            ).value as boolean
          }

          const runRound = () => {
            if (++rounds > MAX_ITERATIONS)
              throw new Unsupported(
                `this loop runs more than ${MAX_ITERATIONS} times, which is too many to unroll`,
                statement,
              )

            this.block(body.kind === K.Block ? body.statements : [body], cur.child(), stop)
          }

          if (statement.kind === K.DoStatement) {
            do {
              runRound()
            } while (check())
          } else {
            while (check()) {
              runRound()
              cur = perIteration(cur)

              if (statement.kind === K.ForStatement && statement.incrementor)
                this.effect(statement.incrementor, cur)
            }
          }

          return rest()
        }

        const test = (cur: Env): Value => {
          const cond = condition ? this.bool(condition, cur) : ir.TRUE
          const goes = this.settle(
            cond,
            () =>
              new Unsupported(
                'how many times this loop runs depends on a value that is not known here',
                condition,
              ),
          )
          return goes.value ? round(cur) : rest()
        }

        const step = (cur: Env): Value => {
          const next = perIteration(cur)

          if (statement.kind === K.ForStatement && statement.incrementor)
            this.effect(statement.incrementor, next)

          return test(next)
        }

        const round = (cur: Env): Value => {
          if (++rounds > MAX_ITERATIONS)
            throw new Unsupported(
              `this loop runs more than ${MAX_ITERATIONS} times, which is too many to unroll`,
              statement,
            )

          return this.block(body.kind === K.Block ? body.statements : [body], cur.child(), {
            next: () => step(cur),
            cont: () => step(cur),
            brk: rest,
          })
        }

        return statement.kind === K.DoStatement ? round(firstEnv) : test(firstEnv)
      }
      case K.ForInStatement:
        throw new Unsupported('for...in loops are not supported', statement)
      case K.TryStatement: {
        if (statement.finallyBlock)
          throw new Unsupported('`finally` is not supported', statement.finallyBlock)

        const catchClause = statement.catchClause

        if (!catchClause || !this.instance)
          throw new Unsupported('try/catch is only supported inside a law', statement)

        if (catchClause.variableDeclaration) {
          if (catchClause.variableDeclaration.name.kind !== K.Identifier) {
            throw new Unsupported(
              'destructuring the caught error in `catch` is not supported',
              catchClause,
            )
          }

          const errName = catchClause.variableDeclaration.name.text as string
          let usedErr = false

          const scan = (n: N) => {
            if (usedErr) return

            if (n.kind === K.Identifier && n.text === errName) {
              usedErr = true
              return
            }

            n.forEachChild(scan)
          }

          scan(catchClause.block)

          if (usedErr)
            throw new Unsupported(
              'reading the caught error in `catch` is not supported',
              catchClause,
            )
        }

        const hasKind = (node: N, kinds: Set<number>): boolean => {
          if (
            !node ||
            node.kind === K.ArrowFunction ||
            node.kind === K.FunctionExpression ||
            node.kind === K.FunctionDeclaration
          )
            return false

          if (kinds.has(node.kind)) return true
          return node.forEachChild((c: N) => hasKind(c, kinds) || undefined) === true
        }

        if (hasKind(statement.tryBlock, new Set([K.BreakStatement, K.ContinueStatement]))) {
          throw new Unsupported(
            '`break` or `continue` inside `try` is not supported',
            statement.tryBlock,
          )
        }

        const THROWING = new Set<ObligationKind>([
          'unreachable',
          'nothrow',
          'undefined',
          'null',
          'tdz',
        ])
        const start = this.instance.obligations.length
        let fellThrough = false
        let tryVal: Value
        this.inThrowCheck++

        try {
          tryVal = this.unchanging('a `try` block', statement, () =>
            this.block(statement.tryBlock.statements, env.child(), {
              next: () => {
                fellThrough = true
                return VOID
              },
            }),
          )
        } finally {
          this.inThrowCheck--
        }

        const added = this.instance.obligations.slice(start)

        if (
          added.some((o) => o.kind === 'expect' || o.kind === 'falloff' || o.kind === 'missing')
        ) {
          throw new Unsupported(
            'a `try` block that calls `expect()`, falls off, or misses a key is not supported',
            statement,
          )
        }

        if (added.some((o) => o.extraBinders && THROWING.has(o.kind))) {
          throw new Unsupported(
            'calling a recursive function that may throw inside `try` is not supported',
            statement,
          )
        }

        const kept: Obligation[] = []
        let threw: Expr = ir.FALSE

        for (const o of added) {
          if (THROWING.has(o.kind)) threw = ir.or(threw, ir.and(o.guard, ir.not(o.claim)))
          else kept.push({ ...o, guard: ir.and(o.guard, ir.not(threw)) })
        }

        this.instance.obligations.splice(start, added.length, ...kept)
        const returnsInTry = hasKind(statement.tryBlock, new Set([K.ReturnStatement]))

        if (fellThrough && returnsInTry)
          throw new Unsupported(
            'a `try` block that returns on only some paths is not supported',
            statement,
          )

        if (!fellThrough) {
          if (threw.t === 'lit') return threw.value ? run(catchClause.block, after) : tryVal
          return this.branch(
            threw,
            () => run(catchClause.block, after),
            () => tryVal,
            true,
          )
        }

        if (threw.t === 'lit') return threw.value ? run(catchClause.block, after) : rest()

        if (canExit(catchClause.block))
          return this.branch(threw, () => run(catchClause.block, after), rest, true)

        this.mergeStates(
          threw,
          () => run(catchClause.block, { next: () => VOID }),
          () => {},
        )
        return rest()
      }
      default:
        throw new Unsupported('this statement is not supported', statement)
    }
  }

  private effect(node: N, env: Env): void {
    if (node.kind === K.ParenthesizedExpression) return this.effect(node.expression, env)

    if (
      node.kind === K.BinaryExpression &&
      node.operatorToken.kind >= K.FirstAssignment &&
      node.operatorToken.kind <= K.LastAssignment
    ) {
      const operator = node.operatorToken.kind
      const base = tables().compound.get(operator)

      if (operator !== K.EqualsToken && base === undefined)
        throw new Unsupported('this assignment operator is not supported', node)

      const place = this.place(node.left, env)

      if (place) {
        const old = base === undefined ? undefined : place.read()
        const right = this.evalExpr(node.right, env)
        place.store(old === undefined ? right : this.arithmetic(base!, old, right, node))
        return
      }

      const cell = this.assignable(node.left, env)
      const old = cell.value
      const right = this.evalExpr(node.right, env)
      cell.value = base === undefined ? right : this.arithmetic(base, old, right, node)
      this.assignedTo?.add(cell)
      return
    }

    if (
      (node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
      (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)
    ) {
      const place = this.place(node.operand, env)

      if (place) {
        const old = place.read()
        place.store(
          this.arithmetic(
            node.operator === K.PlusPlusToken ? K.PlusToken : K.MinusToken,
            old,
            scalar(ir.lit(1n), isNumeric(old)),
            node,
          ),
        )
        return
      }

      const cell = this.assignable(node.operand, env)
      const one = scalar(ir.lit(1n), isNumeric(cell.value))
      cell.value = this.arithmetic(
        node.operator === K.PlusPlusToken ? K.PlusToken : K.MinusToken,
        cell.value,
        one,
        node,
      )
      this.assignedTo?.add(cell)
      return
    }

    if (node.kind === K.CallExpression) {
      if (this.startsWithExpect(node)) return this.expectStatement(node, env)
      this.evalExpr(node, env)
      return
    }

    throw new Unsupported('this statement does nothing that is modeled', node)
  }

  private place(
    target: N,
    env: Env,
  ): { read: () => Value; store: (value: Value) => void } | undefined {
    while (target.kind === K.ParenthesizedExpression || target.kind === K.NonNullExpression)
      target = target.expression

    if (target.kind !== K.PropertyAccessExpression && target.kind !== K.ElementAccessExpression)
      return undefined

    if (target.questionDotToken) throw new Unsupported('optional chaining is not supported', target)

    if (target.kind === K.PropertyAccessExpression && this.isNamespace(target.expression, env))
      throw new Unsupported('assigning to something a module exports is not supported', target)

    const holder = this.evalExpr(target.expression, env)
    const key =
      target.kind === K.PropertyAccessExpression
        ? undefined
        : this.evalExpr(target.argumentExpression, env)

    const slotOf = (object: Value): [Stored, string | number] => {
      if (object.k === 'array' && key) {
        const refusal = () =>
          new Unsupported(
            'an array can only be assigned to at a position that is known here',
            target,
          )

        if (!isNumber(key) || key.k !== 'scalar') throw refusal()
        const position = this.settle(key.e, refusal).value as bigint

        if (position < 0n || position >= BigInt(object.items.length))
          throw new Unsupported(
            'assigning outside the array, which would grow it, is not supported; use `.push`',
            target,
          )

        return [object, Number(position)]
      }

      if (object.k !== 'record')
        throw new Unsupported(
          `assigning to a property of ${describe(object)} is not supported`,
          target,
        )

      const name = key
        ? this.scalarOf(key, target.argumentExpression, 'str')
        : ir.lit(target.name.text as string)
      if (name.t !== 'lit') throw new Error('a key that is not known is settled before this')

      if (name.value === '__proto__')
        throw new Unsupported('assigning to `__proto__` is not modeled', target)

      if (!object.fields.has(name.value as string))
        throw new Unsupported(
          `assigning to \`${name.value}\` would add a property to the object, which is not modeled; give it the property where it is created`,
          target,
        )

      return [object, name.value as string]
    }

    const each = (
      object: Value,
      apply: (stored: Stored, slot: string | number) => Value,
    ): Value => {
      if (object.k === 'bottom') return BOTTOM
      const name =
        object.k === 'record' && key
          ? this.scalarOf(key, target.argumentExpression, 'str')
          : undefined
      if (object.k !== 'record' || !name || name.t === 'lit') return apply(...slotOf(object))
      const names = [...object.fields.keys()]

      const pick = (i: number): Value => {
        if (i === names.length) {
          this.emit('missing', ir.FALSE, target)
          return BOTTOM
        }

        return this.branch(
          ir.eq(name, ir.lit(names[i]!)),
          () => apply(object, names[i]!),
          () => pick(i + 1),
        )
      }

      return pick(0)
    }

    return {
      read: () =>
        this.over(holder, (object) => each(object, (stored, slot) => this.slot(stored, slot)!)),
      store: (value) =>
        void this.over(holder, (object) =>
          each(object, (stored, slot) => {
            this.assertChangeable(stored, value, target)
            this.write(stored, slot, value)
            return VOID
          }),
        ),
    }
  }

  private assignable(target: N, env: Env): Cell {
    if (target.kind === K.ParenthesizedExpression) return this.assignable(target.expression, env)

    if (target.kind !== K.Identifier)
      throw new Unsupported('this assignment target is not supported', target)

    const cell = env.cell(target.text)

    if (!cell)
      throw new Unsupported(
        `\`${target.text}\` is not a local variable, so assigning to it is not supported`,
        target,
      )

    if (!cell.mutable) throw new Unsupported(`\`${target.text}\` cannot be reassigned here`, target)
    return cell
  }

  private scalarOf(value: Value, at: Node, ty?: ir.ScalarTy): Expr {
    if (value.k !== 'scalar')
      throw new Unsupported(
        `expected ${ty ? { bool: 'a boolean', int: 'a bigint', str: 'a string' }[ty] : 'a boolean, bigint or string'} here but found ${describe(value)}`,
        at,
      )

    if (ty && value.e.ty !== ty)
      throw new Unsupported(
        `expected ${{ bool: 'a boolean', int: 'a bigint', str: 'a string' }[ty]} here but found ${describe(value)}`,
        at,
      )

    return value.e
  }

  private bool(node: N, env: Env): Expr {
    return this.truthy(this.evalExpr(node, env), node)
  }

  private truthy(value: Value, at: Node): Expr {
    value = this.settled(value)

    switch (value.k) {
      case 'scalar':
        return value.e.ty === 'bool'
          ? value.e
          : ir.not(ir.eq(value.e, ir.lit(value.e.ty === 'int' ? 0n : '')))
      case 'rat':
      case 'quot':
        return ir.not(ir.eq(value.num, ir.lit(0n)))
      case 'float':
        return ir.lit(value.value !== 0)
      case 'void':
      case 'null':
        return ir.FALSE
      case 'record':
      case 'array':
      case 'list':
      case 'closure':
      case 'infinite':
      case 'map':
      case 'set':
      case 'iterator':
        return ir.TRUE
      case 'choice':
        return ir.ite(value.cond, this.truthy(value.a, at), this.truthy(value.b, at))
      default:
        throw new Unsupported(`${describe(value)} cannot be used as a condition`, at)
    }
  }

  private throwsOnUndefined(at: N): Value {
    this.emit('undefined', ir.FALSE, at)
    return BOTTOM
  }

  private throwsOnNull(at: N): Value {
    this.emit('null', ir.FALSE, at)
    return BOTTOM
  }

  private typeofValue(value: Value, at: N): Value {
    return this.over(value, (part) => {
      switch (part.k) {
        case 'bottom':
          return BOTTOM
        case 'void':
          return scalar(ir.lit('undefined'))
        case 'null':
        case 'record':
        case 'array':
        case 'list':
        case 'map':
        case 'set':
        case 'iterator':
          return scalar(ir.lit('object'))
        case 'closure':
          return scalar(ir.lit('function'))
        case 'infinite':
        case 'rat':
        case 'quot':
        case 'float':
          return scalar(ir.lit('number'))
        case 'scalar':
          return scalar(
            ir.lit(
              part.num
                ? 'number'
                : { bool: 'boolean', int: 'bigint', str: 'string' }[part.e.ty as ir.ScalarTy],
            ),
          )
        default:
          throw new Unsupported(`typeof ${describe(part)} is not supported`, at)
      }
    })
  }

  private defaulted(value: Value, initializer: N, env: Env): Value {
    return this.over(value, (given) =>
      given.k === 'void' ? this.evalExpr(initializer, env) : given,
    )
  }

  private absent(name: string | undefined, at: N): Value {
    if (name !== undefined && name in Object.prototype)
      throw new Unsupported(
        `\`${name}\` is a property every object inherits, which is not modeled`,
        at,
      )

    this.assertBuiltinsIntact(at)
    return VOID
  }

  private wellFormed(text: string, at: Node): string {
    if (!text.isWellFormed())
      throw new Unsupported('string literals with unpaired surrogates are not supported', at)

    return text
  }

  private evalExpr(node: N, env: Env): Value {
    switch (node.kind) {
      case K.NonNullExpression:
        if (inOptionalChain(node)) return this.chain(node, env, (value) => value)
        return this.evalExpr(node.expression, env)
      case K.ParenthesizedExpression:
      case K.AsExpression:
      case K.SatisfiesExpression:
      case K.TypeAssertionExpression:
        return this.evalExpr(node.expression, env)
      case K.StringLiteral:
      case K.NoSubstitutionTemplateLiteral:
        return this.note(ir.lit(this.wellFormed(node.text, node)))
      case K.TrueKeyword:
        return scalar(ir.TRUE)
      case K.FalseKeyword:
        return scalar(ir.FALSE)
      case K.NullKeyword:
        return NULL
      case K.BigIntLiteral:
        return this.note(ir.lit(BigInt(node.text.replace(/n$/, '').replaceAll('_', ''))))
      case K.NumericLiteral: {
        const value = Number(node.text)

        if (!Number.isFinite(value))
          throw new Unsupported('numbers outside the finite double range are not modeled', node)

        return this.fromJsNumber(value, node, true)
      }
      case K.Identifier:
        return this.read(node, env)
      case K.ArrowFunction:
      case K.FunctionExpression:
        return this.makeClosure(node, env)
      case K.TypeOfExpression:
        return this.typeofValue(this.evalExpr(node.expression, env), node)
      case K.PrefixUnaryExpression: {
        if (node.operator === K.ExclamationToken) {
          const operand = this.evalExpr(node.operand, env)
          return operand.k === 'bottom'
            ? BOTTOM
            : scalar(ir.not(this.truthy(operand, node.operand)))
        }

        if (node.operator === K.PlusToken) {
          return this.over(this.evalExpr(node.operand, env), (operand) => {
            if (operand.k === 'bottom') return BOTTOM
            if (operand.k === 'infinite' || isNumeric(operand)) return operand
            throw new Unsupported(
              `unary \`+\` is modeled for numbers, but this is ${describe(operand)}`,
              node,
            )
          })
        }

        if (node.operator === K.MinusToken) {
          return this.over(this.evalExpr(node.operand, env), (operand) => {
            if (operand.k === 'bottom') return BOTTOM
            if (operand.k === 'infinite') return { k: 'infinite', negative: !operand.negative }

            if (operand.k === 'rat')
              return { k: 'rat', num: ir.neg(operand.num), shift: operand.shift }

            if (operand.k === 'quot')
              return { k: 'quot', num: ir.neg(operand.num), den: operand.den }

            if (operand.k === 'float') return this.fromJsNumber(-operand.value, node)
            return scalar(ir.neg(this.scalarOf(operand, node.operand, 'int')), isNumber(operand))
          })
        }

        throw new Unsupported('this operator is not supported', node)
      }
      case K.ConditionalExpression: {
        const condVal = this.evalExpr(node.condition, env)
        if (condVal.k === 'bottom') return BOTTOM
        return this.branch(
          this.truthy(condVal, node.condition),
          () => this.evalExpr(node.whenTrue, env),
          () => this.evalExpr(node.whenFalse, env),
        )
      }
      case K.BinaryExpression:
        return this.binary(node, env)
      case K.TemplateExpression: {
        let result = ir.lit(this.wellFormed(node.head.text, node))

        for (const span of node.templateSpans as N[]) {
          const part = this.text(this.evalExpr(span.expression, env), span.expression, true)
          if (part.k === 'bottom') return BOTTOM
          result = ir.concat(
            ir.concat(result, this.scalarOf(part, span.expression, 'str')),
            ir.lit(this.wellFormed(span.literal.text, span)),
          )
        }

        return scalar(result)
      }
      case K.ObjectLiteralExpression: {
        const parts: (
          | { spread: true; value: Value; node: N }
          | { spread: false; name: string; value: Value }
        )[] = []

        for (const property of node.properties as N[]) {
          if (property.kind === K.SpreadAssignment) {
            const raw = this.evalExpr(property.expression, env)
            if (raw.k === 'bottom') return BOTTOM
            const spread = this.over(raw, (alt) => {
              if (alt.k === 'bottom') return BOTTOM
              if (alt.k === 'void' || alt.k === 'null') return alt

              if (alt.k !== 'record')
                throw new Unsupported(`cannot spread ${describe(alt)} into an object`, property)

              return this.fresh({
                k: 'record',
                fields: new Map(alt.fields),
                ...(alt.unordered ? { unordered: true } : {}),
              })
            })
            if (spread.k === 'bottom') return BOTTOM
            parts.push({ spread: true, value: spread, node: property })
          } else if (property.kind === K.ShorthandPropertyAssignment) {
            const val = this.read(property.name, env, true)
            if (val.k === 'bottom') return BOTTOM
            parts.push({ spread: false, name: property.name.text, value: val })
          } else if (
            property.kind === K.PropertyAssignment &&
            (property.name.kind === K.Identifier ||
              property.name.kind === K.StringLiteral ||
              property.name.kind === K.NumericLiteral)
          ) {
            const propName =
              property.name.kind === K.NumericLiteral
                ? String(Number(property.name.text))
                : (property.name.text as string)

            if (propName === '__proto__')
              throw new Unsupported(
                '`__proto__` in an object literal sets the prototype, which is not modeled',
                property,
              )

            const val = this.evalExpr(property.initializer, env)
            if (val.k === 'bottom') return BOTTOM
            parts.push({ spread: false, name: propName, value: val })
          } else
            throw new Unsupported(
              'methods, accessors and computed property names are not supported in object literals',
              property,
            )
        }

        let shapes = 0

        const build = (
          from: number,
          before: Map<string, Value>,
          unorderedBefore: boolean,
        ): Value => {
          if (++shapes > MAX_ALTERNATIVES) {
            throw new Unsupported(
              `an object literal with more than ${MAX_ALTERNATIVES} conditional spread combinations is not supported`,
              node,
            )
          }

          const fields = new Map(before)
          let unordered = unorderedBefore

          for (let index = from; index < parts.length; index++) {
            const part = parts[index]!

            if (!part.spread) {
              fields.set(part.name, part.value)
              continue
            }

            const spread = this.settled(part.value)

            if (spread.k === 'choice') {
              return this.over(spread, (alt) => {
                if (alt.k === 'bottom') return BOTTOM
                if (alt.k === 'void' || alt.k === 'null') return build(index + 1, fields, unordered)

                if (alt.k !== 'record')
                  throw new Unsupported(`cannot spread ${describe(alt)} into an object`, part.node)

                const next = new Map(fields)
                for (const [k, v] of alt.fields) next.set(k, v)
                return build(index + 1, next, unordered || (!!alt.unordered && alt.fields.size > 0))
              })
            }

            if (spread.k === 'bottom') return BOTTOM
            if (spread.k === 'void' || spread.k === 'null') continue

            if (spread.k !== 'record')
              throw new Unsupported(`cannot spread ${describe(spread)} into an object`, part.node)

            if (spread.unordered && spread.fields.size > 0) unordered = true
            for (const [key, field] of spread.fields) fields.set(key, field)
          }

          return this.fresh({ k: 'record', fields, ...(unordered ? { unordered: true } : {}) })
        }

        return build(0, new Map(), false)
      }
      case K.ArrayLiteralExpression: {
        const parts: { spread: boolean; value: Value }[] = []

        for (const element of node.elements as N[]) {
          if (element.kind === K.OmittedExpression)
            throw new Unsupported('array holes are not supported', node)

          if (element.kind !== K.SpreadElement) {
            const val = this.evalExpr(element, env)
            if (val.k === 'bottom') return BOTTOM
            parts.push({ spread: false, value: val })
          } else {
            const raw = this.evalExpr(element.expression, env)
            const val =
              this.settled(raw).k === 'list'
                ? raw
                : this.copied(raw, element, 'cannot spread', 'into an array')
            if (val.k === 'bottom') return BOTTOM
            parts.push({ spread: true, value: val })
          }
        }

        const hasSymList = (v: Value): boolean =>
          v.k === 'list' || (v.k === 'choice' && (hasSymList(v.a) || hasSymList(v.b)))

        if (parts.some((p) => p.spread && hasSymList(p.value))) {
          const buildSym = (
            from: number,
            acc: Extract<Value, { k: 'list' }> | undefined,
            pending: Value[],
          ): Value => {
            if (from === parts.length) {
              if (!acc) return this.fresh({ k: 'array', items: pending })
              if (!pending.length) return acc
              const tail = this.asListExpr(
                { k: 'array', items: pending },
                acc.e.ty as ir.ListTy,
                !!acc.num,
              )

              if (!tail)
                throw new Unsupported(
                  'spreading an arbitrary-length array with elements of a different type is not supported',
                  node,
                )

              return {
                k: 'list',
                e: ir.listConcat(acc.e, tail.e),
                ...(acc.num ? { num: true } : {}),
              }
            }

            const part = parts[from]!
            if (!part.spread) return buildSym(from + 1, acc, [...pending, part.value])
            return this.over(part.value, (spread) => {
              if (spread.k === 'bottom') return BOTTOM

              if (spread.k === 'array')
                return buildSym(from + 1, acc, [...pending, ...spread.items])

              if (spread.k !== 'list') return BOTTOM
              let next: Extract<Value, { k: 'list' }> = spread

              if (pending.length) {
                const head = this.asListExpr(
                  { k: 'array', items: pending },
                  spread.e.ty as ir.ListTy,
                  !!spread.num,
                )

                if (!head)
                  throw new Unsupported(
                    'spreading an arbitrary-length array with elements of a different type is not supported',
                    node,
                  )

                next = {
                  k: 'list',
                  e: ir.listConcat(head.e, next.e),
                  ...(spread.num ? { num: true } : {}),
                }
              }

              if (acc) {
                if (acc.e.ty !== next.e.ty || !!acc.num !== !!next.num)
                  throw new Unsupported(
                    'spreading arbitrary-length arrays of different element types is not supported',
                    node,
                  )

                next = {
                  k: 'list',
                  e: ir.listConcat(acc.e, next.e),
                  ...(acc.num ? { num: true } : {}),
                }
              }

              return buildSym(from + 1, next, [])
            })
          }

          return buildSym(0, undefined, [])
        }

        const join = (from: number, before: Value[]): Value => {
          const items = [...before]
          let index = from

          for (; index < parts.length; index++) {
            const part = parts[index]!

            if (!part.spread) {
              items.push(part.value)
              continue
            }

            const copy = this.settled(part.value)
            if (copy.k === 'choice') break
            if (copy.k !== 'array') return BOTTOM
            items.push(...copy.items)
          }

          if (index === parts.length) return this.fresh({ k: 'array', items })
          return this.over(parts[index]!.value, (copy) =>
            copy.k === 'array' ? join(index + 1, [...items, ...copy.items]) : BOTTOM,
          )
        }

        return join(0, [])
      }
      case K.PropertyAccessExpression:
        if (inOptionalChain(node)) return this.chain(node, env, (value) => value)

        if (
          node.expression.kind === K.Identifier &&
          node.expression.text === 'Number' &&
          !env.get('Number') &&
          this.isBuiltin(node.expression)
        ) {
          if (node.name.text === 'MAX_SAFE_INTEGER') return scalar(ir.lit(ir.MAX_SAFE), true)
          if (node.name.text === 'MIN_SAFE_INTEGER') return scalar(ir.lit(-ir.MAX_SAFE), true)
        }

        if (this.isNamespace(node.expression, env)) return this.global(node.name)
        return this.over(this.evalExpr(node.expression, env), (object) =>
          this.property(object, node),
        )
      case K.ElementAccessExpression:
        if (inOptionalChain(node)) return this.chain(node, env, (value) => value)
        return this.over(this.evalExpr(node.expression, env), (object) =>
          this.element(object, node, env),
        )
      case K.CallExpression:
        if (inOptionalChain(node)) return this.chain(node, env, (value) => value)
        return this.callExpression(node, env)
      case K.NewExpression:
        return this.construct(node, env)
      default:
        throw new Unsupported('this expression is not supported', node)
    }
  }

  private note(literal: Expr, num = false): Value {
    if (this.mentioned.length < 256) this.mentioned.push(literal)
    return scalar(literal, num)
  }

  private read(node: N, env: Env, shorthand = false): Value {
    const local = env.get(node.text)

    if (local?.k === 'uninitialized') {
      this.emit('tdz', ir.FALSE, node)
      return BOTTOM
    }

    if (local) return this.settled(local)

    if (node.text === 'undefined') {
      const symbol = shorthand ? undefined : this.checker.getSymbolAtLocation(node)
      if (symbol && this.checker.isUndefinedSymbol(symbol)) return VOID
    }

    if (node.text === 'Infinity' && !shorthand && this.isBuiltin(node))
      return { k: 'infinite', negative: false }

    return this.global(node, shorthand)
  }

  private settled(value: Value): Value {
    if (value.k !== 'choice') return value
    const known: Expr[] = []

    const learn = (e: Expr) => {
      if (e.t === 'op' && e.op === 'and') e.args.forEach(learn)
      else if (e.t === 'op' && e.op === 'not' && e.args[0]!.t === 'op' && e.args[0]!.op === 'or')
        e.args[0]!.args.forEach((arg) => learn(ir.not(arg)))
      else known.push(e)
    }

    this.pc.forEach(learn)

    while (value.k === 'choice') {
      const cond = value.cond

      if (known.some((fact) => ir.same(fact, cond))) value = value.a
      else {
        const negated = ir.not(cond)

        if (known.some((fact) => ir.same(fact, negated))) value = value.b
        else break
      }
    }

    return value
  }

  private strictEqual(a: Value, b: Value, at: Node): Expr {
    if (a.k === 'void' || b.k === 'void')
      return a.k === b.k
        ? ir.TRUE
        : (this.isPlain(a) || isObject(a)) && (this.isPlain(b) || isObject(b))
          ? ir.FALSE
          : this.refuseEquality(a, b, at)

    if (a.k === 'null' || b.k === 'null')
      return a.k === b.k
        ? ir.TRUE
        : (this.isPlain(a) || isObject(a)) && (this.isPlain(b) || isObject(b))
          ? ir.FALSE
          : this.refuseEquality(a, b, at)

    if (a.k === 'infinite' || b.k === 'infinite') {
      if (a.k === 'infinite' && b.k === 'infinite') return ir.lit(a.negative === b.negative)
      return this.isPlain(a) && this.isPlain(b) ? ir.FALSE : this.refuseEquality(a, b, at)
    }

    if (isNumeric(a) && isNumeric(b))
      return this.compareNumeric(K.EqualsEqualsEqualsToken, a, b, at)

    if (isNumeric(a) || isNumeric(b))
      return this.isPlain(a) && this.isPlain(b) ? ir.FALSE : this.refuseEquality(a, b, at)

    if (a.k !== 'scalar' || b.k !== 'scalar') return this.refuseEquality(a, b, at)
    return a.e.ty === b.e.ty && !!a.num === !!b.num ? ir.eq(a.e, b.e) : ir.FALSE
  }

  private eqValues(a: Value, b: Value, at: Node): Value {
    if (a.k === 'bottom' || b.k === 'bottom') return BOTTOM
    return this.over(a, (left) =>
      this.over(b, (right) =>
        left.k === 'bottom' || right.k === 'bottom'
          ? BOTTOM
          : scalar(this.strictEqual(left, right, at)),
      ),
    )
  }

  private arrayContains(items: Value[], needle: Value, at: Node): Value {
    if (needle.k === 'bottom') return BOTTOM
    let acc: Expr = ir.FALSE

    for (const item of items) {
      const eq = this.eqValues(item, needle, at)
      if (eq.k === 'bottom') return BOTTOM
      acc = ir.or(acc, this.scalarOf(eq, at, 'bool'))
    }

    return scalar(acc)
  }

  private isPlain(value: Value): boolean {
    return (
      value.k === 'scalar' ||
      value.k === 'rat' ||
      value.k === 'quot' ||
      value.k === 'float' ||
      value.k === 'void' ||
      value.k === 'null' ||
      value.k === 'infinite'
    )
  }

  private refuseEquality(a: Value, b: Value, at: Node): never {
    throw new Unsupported(
      `comparing ${describe(a)} with ${describe(b)} is not modeled; only booleans, bigints, numbers, strings, null and undefined are compared by ===`,
      at,
    )
  }

  private binary(node: N, env: Env): Value {
    const operator = node.operatorToken.kind

    if (
      operator === K.AmpersandAmpersandToken ||
      operator === K.BarBarToken ||
      operator === K.QuestionQuestionToken
    ) {
      const symbol =
        operator === K.AmpersandAmpersandToken ? '&&' : operator === K.BarBarToken ? '||' : '??'

      const right = () =>
        this.unchanging(`the right side of \`${symbol}\``, node.right, () =>
          this.evalExpr(node.right, env),
        )

      return this.over(this.evalExpr(node.left, env), (left) => {
        if (left.k === 'bottom') return BOTTOM

        if (operator === K.QuestionQuestionToken)
          return left.k === 'void' || left.k === 'null' ? right() : left

        const taken = this.truthy(left, node.left)

        const known = (value: boolean) =>
          left.k === 'scalar'
            ? left.e.ty === 'bool'
              ? scalar(ir.lit(value))
              : value
                ? left
                : scalar(ir.lit(left.e.ty === 'int' ? 0n : ''), left.num)
            : left.k === 'rat' || left.k === 'quot' || left.k === 'float'
              ? value
                ? left
                : scalar(ir.lit(0n), true)
              : left

        return operator === K.AmpersandAmpersandToken
          ? this.branch(taken, right, () => known(false))
          : this.branch(taken, () => known(true), right)
      })
    }

    const leftValue = this.evalExpr(node.left, env)
    const rightValue = this.evalExpr(node.right, env)

    if (operator === K.InKeyword) {
      return this.over(rightValue, (obj) =>
        this.over(leftValue, (keyVal) => {
          if (obj.k === 'bottom' || keyVal.k === 'bottom') return BOTTOM
          if (obj.k === 'void') return this.throwsOnUndefined(node)
          if (obj.k === 'null') return this.throwsOnNull(node)
          this.assertBuiltinsIntact(node)

          if (obj.k === 'array') {
            const key =
              keyVal.k === 'scalar' && keyVal.e.ty === 'str'
                ? keyVal.e
                : isNumber(keyVal) && keyVal.k === 'scalar'
                  ? ir.toStr(keyVal.e)
                  : undefined

            if (!key)
              throw new Unsupported(
                `\`in\` with ${describe(keyVal)} on an array is not supported`,
                node,
              )

            const lit = this.settle(
              key,
              () => new Unsupported('`in` on an array requires a known key or index', node),
            ).value as string

            if (lit === 'length' || (isArrayIndexKey(lit) && Number(lit) < obj.items.length))
              return scalar(ir.TRUE)

            if (lit in Array.prototype)
              throw new Unsupported(
                `\`${lit}\` is a property every array inherits, which is not modeled`,
                node,
              )

            return scalar(ir.FALSE)
          }

          if (obj.k !== 'record')
            throw new Unsupported(`\`in\` on ${describe(obj)} is not supported`, node)

          const key =
            keyVal.k === 'scalar' && keyVal.e.ty === 'str'
              ? keyVal.e
              : isNumber(keyVal) && keyVal.k === 'scalar'
                ? ir.toStr(keyVal.e)
                : undefined

          if (!key)
            throw new Unsupported(
              `\`in\` expects a string or number key, but found ${describe(keyVal)}`,
              node.left,
            )

          if (key.t === 'lit') {
            const name = key.value as string
            if (obj.fields.has(name)) return scalar(ir.TRUE)

            if (name in Object.prototype)
              throw new Unsupported(
                `\`${name}\` is a property every object inherits, which is not modeled`,
                node,
              )

            return scalar(ir.FALSE)
          }

          const names = [...obj.fields.keys()]
          const inherited = Object.getOwnPropertyNames(Object.prototype).filter(
            (name) => !obj.fields.has(name),
          )
          this.emit(
            'inherited',
            ir.not(inherited.map((name) => ir.eq(key, ir.lit(name))).reduce(ir.or, ir.FALSE)),
            node,
          )
          return scalar(names.map((name) => ir.eq(key, ir.lit(name))).reduce(ir.or, ir.FALSE))
        }),
      )
    }

    if (operator === K.EqualsEqualsEqualsToken || operator === K.ExclamationEqualsEqualsToken) {
      const equal = this.eqValues(leftValue, rightValue, node)
      if (equal.k === 'bottom') return BOTTOM
      const same = this.scalarOf(equal, node, 'bool')
      return scalar(operator === K.EqualsEqualsEqualsToken ? same : ir.not(same))
    }

    if (operator === K.EqualsEqualsToken || operator === K.ExclamationEqualsToken)
      throw new Unsupported('use === and !==; loose equality is not modeled', node)

    if (operator >= K.FirstAssignment && operator <= K.LastAssignment)
      throw new Unsupported(
        'an assignment used as a value is not supported; write it as its own statement',
        node,
      )

    return this.arithmetic(operator, leftValue, rightValue, node)
  }

  private fromJsNumber(value: number, node: Node, note = false): Value {
    if (Number.isSafeInteger(value)) {
      const lit = ir.lit(BigInt(value))
      return note ? this.note(lit, true) : scalar(lit, true)
    }

    const dyadic = dyadicOf(value)
    if (dyadic) return { k: 'rat', num: ir.lit(dyadic.num), shift: dyadic.shift }
    return { k: 'float', value }
  }

  private makeRat(num: Expr, shift: number, node: Node): Value {
    if (num.t === 'lit') {
      let n = num.value as bigint

      while (shift > 0 && (n & 1n) === 0n) {
        n >>= 1n
        shift--
      }

      num = ir.lit(n)
    } else {
      while (
        shift > 0 &&
        num.t === 'op' &&
        num.op === 'mul' &&
        num.args[1]!.t === 'lit' &&
        ((num.args[1]!.value as bigint) & 1n) === 0n
      ) {
        const half = (num.args[1]!.value as bigint) >> 1n
        num = ir.mul(num.args[0]!, ir.lit(half))
        shift--
      }
    }

    if (shift === 0) {
      this.emit('overflow', ir.isSafe(num), node)
      return scalar(num, true)
    }

    if (shift > MAX_DYADIC_SHIFT) {
      if (num.t === 'lit') {
        const v = Number(num.value as bigint) / 2 ** shift

        if (!Number.isFinite(v)) {
          this.emit('overflow', ir.FALSE, node)
          return BOTTOM
        }

        return this.fromJsNumber(v, node)
      }

      throw new Unsupported(
        'fractional binary precision past 2^-10 is not modeled unless the values are known here',
        node,
      )
    }

    this.emit('overflow', ir.isSafe(num), node)
    return { k: 'rat', num, shift }
  }

  private knownNumber(value: Value): number | undefined {
    if (value.k === 'float') return value.value
    if (value.k === 'scalar' && value.num && value.e.t === 'lit') return Number(value.e.value)

    if (value.k === 'rat' && value.num.t === 'lit')
      return Number(value.num.value) / 2 ** value.shift

    if (
      value.k === 'quot' &&
      value.num.t === 'lit' &&
      value.den.t === 'lit' &&
      value.den.value !== 0n
    ) {
      return Number(value.num.value) / Number(value.den.value)
    }

    return undefined
  }

  private settleNumber(value: Value, refusal: () => Unsupported): number {
    if (value.k === 'float') return value.value
    if (value.k === 'scalar' && value.num) return Number(this.settle(value.e, refusal).value)
    if (value.k === 'rat') return Number(this.settle(value.num, refusal).value) / 2 ** value.shift

    if (value.k === 'quot') {
      const n = Number(this.settle(value.num, refusal).value)
      const d = Number(this.settle(value.den, refusal).value)
      return n / d
    }

    throw refusal()
  }

  private compareNumeric(op: number, left: Value, right: Value, node: Node): Expr {
    const lk = this.knownNumber(left)
    const rk = this.knownNumber(right)

    if (lk !== undefined && rk !== undefined) {
      return ir.lit(
        op === K.EqualsEqualsEqualsToken
          ? lk === rk
          : op === K.LessThanToken
            ? lk < rk
            : op === K.LessThanEqualsToken
              ? lk <= rk
              : op === K.GreaterThanToken
                ? lk > rk
                : lk >= rk,
      )
    }

    const cmpInt = (a: Expr, b: Expr, operator: number): Expr =>
      operator === K.EqualsEqualsEqualsToken
        ? ir.eq(a, b)
        : operator === K.LessThanToken
          ? ir.lt(a, b)
          : operator === K.LessThanEqualsToken
            ? ir.le(a, b)
            : operator === K.GreaterThanToken
              ? ir.lt(b, a)
              : ir.le(b, a)

    const flip = (operator: number): number =>
      operator === K.LessThanToken
        ? K.GreaterThanToken
        : operator === K.LessThanEqualsToken
          ? K.GreaterThanEqualsToken
          : operator === K.GreaterThanToken
            ? K.LessThanToken
            : operator === K.GreaterThanEqualsToken
              ? K.LessThanEqualsToken
              : operator

    if ((isNumber(left) || left.k === 'rat') && (isNumber(right) || right.k === 'rat')) {
      const n1 = left.k === 'rat' ? left.num : (left as Extract<Value, { k: 'scalar' }>).e
      const s1 = left.k === 'rat' ? left.shift : 0
      const n2 = right.k === 'rat' ? right.num : (right as Extract<Value, { k: 'scalar' }>).e
      const s2 = right.k === 'rat' ? right.shift : 0
      const s = Math.max(s1, s2)
      const a = s > s1 ? ir.mul(n1, ir.lit(2n ** BigInt(s - s1))) : n1
      const b = s > s2 ? ir.mul(n2, ir.lit(2n ** BigInt(s - s2))) : n2
      return cmpInt(a, b, op)
    }

    if ((left.k === 'quot' && isNumber(right)) || (isNumber(left) && right.k === 'quot')) {
      const q = (left.k === 'quot' ? left : right) as Extract<Value, { k: 'quot' }>
      const c = ((left.k === 'quot' ? right : left) as Extract<Value, { k: 'scalar' }>).e
      const o = left.k === 'quot' ? op : flip(op)
      const rhs = ir.mul(q.den, c)
      if (o === K.EqualsEqualsEqualsToken) return ir.eq(q.num, rhs)
      return ir.ite(ir.lt(ir.lit(0n), q.den), cmpInt(q.num, rhs, o), cmpInt(q.num, rhs, flip(o)))
    }

    if (left.k === 'quot' && right.k === 'quot') {
      if (
        op === K.EqualsEqualsEqualsToken &&
        ir.same(left.num, right.num) &&
        ir.same(left.den, right.den)
      )
        return ir.TRUE

      const refusal = () =>
        new Unsupported(
          'comparing two divisions can depend on floating-point rounding, which is not modeled unless their values are known here',
          node,
        )

      const a = this.settleNumber(left, refusal)
      const b = this.settleNumber(right, refusal)
      return ir.lit(
        op === K.EqualsEqualsEqualsToken
          ? a === b
          : op === K.LessThanToken
            ? a < b
            : op === K.LessThanEqualsToken
              ? a <= b
              : op === K.GreaterThanToken
                ? a > b
                : a >= b,
      )
    }

    if (
      (left.k === 'float' && (isNumber(right) || right.k === 'rat')) ||
      ((isNumber(left) || left.k === 'rat') && right.k === 'float')
    ) {
      const f = (left.k === 'float' ? left : right) as Extract<Value, { k: 'float' }>
      const other = left.k === 'float' ? right : left
      const o = left.k === 'float' ? flip(op) : op
      const x = other.k === 'rat' ? other.num : (other as Extract<Value, { k: 'scalar' }>).e
      const shift = other.k === 'rat' ? other.shift : 0
      const scaled = f.value * 2 ** shift

      if (!Number.isFinite(scaled)) {
        if (o === K.EqualsEqualsEqualsToken) return ir.FALSE
        return ir.lit(
          o === K.LessThanToken || o === K.LessThanEqualsToken ? scaled > 0 : scaled < 0,
        )
      }

      if (Number.isSafeInteger(scaled)) return cmpInt(x, ir.lit(BigInt(scaled)), o)

      if (!Number.isInteger(scaled)) {
        if (o === K.EqualsEqualsEqualsToken) return ir.FALSE

        if (o === K.LessThanToken || o === K.LessThanEqualsToken)
          return ir.le(x, ir.lit(BigInt(Math.floor(scaled))))

        return ir.le(ir.lit(BigInt(Math.ceil(scaled))), x)
      }

      if (o === K.EqualsEqualsEqualsToken) return ir.FALSE
      return ir.lit(o === K.LessThanToken || o === K.LessThanEqualsToken ? scaled > 0 : scaled < 0)
    }

    const refusal = () =>
      new Unsupported(
        'comparing a division with a fraction can depend on floating-point rounding, which is not modeled unless the values are known here',
        node,
      )

    const a = this.settleNumber(left, refusal)
    const b = this.settleNumber(right, refusal)
    return ir.lit(
      op === K.EqualsEqualsEqualsToken
        ? a === b
        : op === K.LessThanToken
          ? a < b
          : op === K.LessThanEqualsToken
            ? a <= b
            : op === K.GreaterThanToken
              ? a > b
              : a >= b,
    )
  }

  private arithmetic(operator: number, leftValue: Value, rightValue: Value, node: N): Value {
    if (leftValue.k === 'choice' || rightValue.k === 'choice') {
      return this.over(leftValue, (left) =>
        this.over(rightValue, (right) => this.arithmetic(operator, left, right, node)),
      )
    }

    if (leftValue.k === 'bottom' || rightValue.k === 'bottom') return BOTTOM

    if (leftValue.k === 'infinite' || rightValue.k === 'infinite') {
      const rank = (value: Value) =>
        value.k === 'infinite' ? (value.negative ? -1 : 1) : isNumeric(value) ? 0 : undefined

      const left = rank(leftValue)
      const right = rank(rightValue)
      const result =
        left === undefined || right === undefined
          ? undefined
          : operator === K.LessThanToken
            ? left < right
            : operator === K.LessThanEqualsToken
              ? left <= right
              : operator === K.GreaterThanToken
                ? left > right
                : operator === K.GreaterThanEqualsToken
                  ? left >= right
                  : undefined

      if (result === undefined)
        throw new Unsupported('Infinity is only modeled where it is compared with a number', node)

      return scalar(ir.lit(result))
    }

    if (
      operator === K.PlusToken &&
      leftValue.k === 'scalar' &&
      rightValue.k === 'scalar' &&
      leftValue.e.ty === 'str' &&
      rightValue.e.ty === 'str'
    ) {
      return scalar(ir.concat(leftValue.e, rightValue.e))
    }

    const isComparison =
      operator === K.LessThanToken ||
      operator === K.LessThanEqualsToken ||
      operator === K.GreaterThanToken ||
      operator === K.GreaterThanEqualsToken

    if (isNumeric(leftValue) || isNumeric(rightValue)) {
      if (!isNumeric(leftValue) || !isNumeric(rightValue))
        throw new Unsupported(
          `cannot combine ${describe(leftValue)} with ${describe(rightValue)}`,
          node,
        )

      if (isComparison) return scalar(this.compareNumeric(operator, leftValue, rightValue, node))

      if (leftValue.k !== 'scalar' || rightValue.k !== 'scalar' || operator === K.SlashToken) {
        return this.fractionalArithmetic(operator, leftValue, rightValue, node)
      }
    }

    const left = this.scalarOf(leftValue, node.left ?? node, 'int')
    const right = this.scalarOf(rightValue, node.right ?? node, 'int')

    if (isNumber(leftValue) !== isNumber(rightValue))
      throw new Unsupported(
        `cannot combine ${describe(leftValue)} with ${describe(rightValue)}`,
        node,
      )

    if (operator === K.AsteriskAsteriskToken) {
      const exp = this.settle(
        right,
        () => new Unsupported('exponentiation requires an exponent known here', node),
      ).value as bigint

      if (exp < 0n) {
        if (!isNumber(leftValue)) {
          this.emit('unreachable', ir.FALSE, node)
          return BOTTOM
        }

        const base = Number(
          this.settle(
            left,
            () => new Unsupported('negative exponents on numbers require values known here', node),
          ).value,
        )

        if (base === 0) {
          this.emit('nan', ir.FALSE, node)
          return BOTTOM
        }

        const res = base ** Number(exp)

        if (!Number.isFinite(res)) {
          this.emit('overflow', ir.FALSE, node)
          return BOTTOM
        }

        return this.fromJsNumber(res, node)
      }

      const num = isNumber(leftValue)

      const exactNum = (result: Expr) => {
        if (num) this.emit('overflow', ir.isSafe(result), node)
        return scalar(result, num)
      }

      if (exp === 0n) return scalar(ir.lit(1n), num)
      if (exp === 1n) return scalar(left, num)

      if (left.t === 'lit') {
        if (exp > 64n) throw new Unsupported('exponent is too large to model', node)
        return exactNum(ir.lit((left.value as bigint) ** exp))
      }

      if (exp > 8n)
        throw new Unsupported(
          'exponentiation of an unknown value is modeled up to exponent 8',
          node,
        )

      let acc: Expr = left
      for (let i = 1n; i < exp; i++) acc = ir.mul(acc, left)
      return exactNum(acc)
    }

    if (isNumber(leftValue)) {
      const exact = (result: Expr) => {
        this.emit('overflow', ir.isSafe(result), node)
        return scalar(result, true)
      }

      switch (operator) {
        case K.PlusToken:
          return exact(ir.add(left, right))
        case K.MinusToken:
          return exact(ir.sub(left, right))
        case K.AsteriskToken:
          return exact(ir.mul(left, right))
        case K.PercentToken:
          this.emit('nan', ir.not(ir.eq(right, ir.lit(0n))), node)
          return scalar(ir.mod(left, right), true)
      }
    }

    switch (operator) {
      case K.PlusToken:
        return scalar(ir.add(left, right))
      case K.MinusToken:
        return scalar(ir.sub(left, right))
      case K.AsteriskToken:
        return scalar(ir.mul(left, right))
      case K.SlashToken:
      case K.PercentToken:
        this.emit('nothrow', ir.not(ir.eq(right, ir.lit(0n))), node)
        return scalar(operator === K.SlashToken ? ir.div(left, right) : ir.mod(left, right))
      case K.LessThanToken:
        return scalar(ir.lt(left, right))
      case K.LessThanEqualsToken:
        return scalar(ir.le(left, right))
      case K.GreaterThanToken:
        return scalar(ir.lt(right, left))
      case K.GreaterThanEqualsToken:
        return scalar(ir.le(right, left))
      default:
        throw new Unsupported('this operator is not supported', node)
    }
  }

  private fractionalArithmetic(
    operator: number,
    leftValue: Value,
    rightValue: Value,
    node: N,
  ): Value {
    const evalKnownFloat = (a: number, b: number): Value => {
      if ((operator === K.SlashToken || operator === K.PercentToken) && b === 0) {
        this.emit('nan', ir.FALSE, node)
        return BOTTOM
      }

      let res: number

      switch (operator) {
        case K.PlusToken:
          res = a + b
          break
        case K.MinusToken:
          res = a - b
          break
        case K.AsteriskToken:
          res = a * b
          break
        case K.SlashToken:
          res = a / b
          break
        case K.PercentToken:
          res = a % b
          break
        case K.AsteriskAsteriskToken:
          res = a ** b
          break
        default:
          throw new Unsupported('this operator is not supported', node)
      }

      if (Number.isNaN(res)) {
        this.emit('nan', ir.FALSE, node)
        return BOTTOM
      }

      if (!Number.isFinite(res)) {
        this.emit('overflow', ir.FALSE, node)
        return BOTTOM
      }

      return this.fromJsNumber(res, node)
    }

    const lk = this.knownNumber(leftValue)
    const rk = this.knownNumber(rightValue)
    if (lk !== undefined && rk !== undefined) return evalKnownFloat(lk, rk)

    if (
      (isNumber(leftValue) || leftValue.k === 'rat') &&
      (isNumber(rightValue) || rightValue.k === 'rat')
    ) {
      const n1 =
        leftValue.k === 'rat' ? leftValue.num : (leftValue as Extract<Value, { k: 'scalar' }>).e
      const s1 = leftValue.k === 'rat' ? leftValue.shift : 0
      const n2 =
        rightValue.k === 'rat' ? rightValue.num : (rightValue as Extract<Value, { k: 'scalar' }>).e
      const s2 = rightValue.k === 'rat' ? rightValue.shift : 0

      if (operator === K.PlusToken || operator === K.MinusToken) {
        const s = Math.max(s1, s2)
        const a = s > s1 ? ir.mul(n1, ir.lit(2n ** BigInt(s - s1))) : n1
        const b = s > s2 ? ir.mul(n2, ir.lit(2n ** BigInt(s - s2))) : n2
        return this.makeRat(operator === K.PlusToken ? ir.add(a, b) : ir.sub(a, b), s, node)
      }

      if (operator === K.AsteriskToken) {
        return this.makeRat(ir.mul(n1, n2), s1 + s2, node)
      }

      if (operator === K.PercentToken) {
        this.emit('nan', ir.not(ir.eq(n2, ir.lit(0n))), node)
        const s = Math.max(s1, s2)
        const a = s > s1 ? ir.mul(n1, ir.lit(2n ** BigInt(s - s1))) : n1
        const b = s > s2 ? ir.mul(n2, ir.lit(2n ** BigInt(s - s2))) : n2
        return this.makeRat(ir.mod(a, b), s, node)
      }

      if (operator === K.SlashToken) {
        if (s2 === 0 && n2.t === 'lit') {
          const p2 = pow2Of(n2.value as bigint)
          if (p2) return this.makeRat(p2.negative ? ir.neg(n1) : n1, s1 + p2.shift, node)
        }

        if (rightValue.k === 'rat' && n2.t === 'lit' && (n2.value === 1n || n2.value === -1n)) {
          const signed = n2.value < 0n ? ir.neg(n1) : n1
          if (s1 >= s2) return this.makeRat(signed, s1 - s2, node)
          return this.makeRat(ir.mul(signed, ir.lit(2n ** BigInt(s2 - s1))), 0, node)
        }

        if (s1 === 0 && s2 === 0) {
          this.emit('nan', ir.not(ir.eq(n2, ir.lit(0n))), node)
          return { k: 'quot', num: n1, den: n2 }
        }
      }

      if (operator === K.AsteriskAsteriskToken && s2 === 0) {
        const exp = this.settle(
          n2,
          () => new Unsupported('exponentiation requires an exponent known here', node),
        ).value as bigint
        if (exp === 0n) return scalar(ir.lit(1n), true)
        if (exp === 1n) return leftValue

        if (exp > 0n && exp <= 8n && s1 * Number(exp) <= MAX_DYADIC_SHIFT) {
          let acc: Expr = n1
          for (let i = 1n; i < exp; i++) acc = ir.mul(acc, n1)
          return this.makeRat(acc, s1 * Number(exp), node)
        }
      }
    }

    if (
      (operator === K.AsteriskToken || operator === K.SlashToken) &&
      (leftValue.k === 'quot' || (operator === K.AsteriskToken && rightValue.k === 'quot'))
    ) {
      const q = (leftValue.k === 'quot' ? leftValue : rightValue) as Extract<Value, { k: 'quot' }>
      const other = leftValue.k === 'quot' ? rightValue : leftValue

      if (isNumber(other) && other.k === 'scalar' && other.e.t === 'lit') {
        const p2 = pow2Of(other.e.value as bigint)

        if (p2) {
          const factor = 2n ** BigInt(p2.shift)

          if (operator === K.AsteriskToken) {
            const scaled = ir.mul(p2.negative ? ir.neg(q.num) : q.num, ir.lit(factor))
            this.emit('overflow', ir.isSafe(scaled), node)
            return { k: 'quot', num: scaled, den: q.den }
          }

          const scaledDen = ir.mul(p2.negative ? ir.neg(q.den) : q.den, ir.lit(factor))
          this.emit('overflow', ir.isSafe(scaledDen), node)
          return { k: 'quot', num: q.num, den: scaledDen }
        }
      }
    }

    const refusal = () =>
      new Unsupported(
        leftValue.k === 'float' || rightValue.k === 'float'
          ? 'arithmetic with a non-dyadic decimal requires inputs whose values are known here; use integer scaling like Math.round((x * 15) / 100) for large ranges'
          : 'further arithmetic on a division can double-round in IEEE-754, which is not modeled unless the values are known here',
        node,
      )

    const a = this.settleNumber(leftValue, refusal)
    const b = this.settleNumber(rightValue, refusal)
    return evalKnownFloat(a, b)
  }

  private property(object: Value, node: N): Value {
    const name = node.name.text as string
    if (name === '__proto__') throw new Unsupported('reading `__proto__` is not modeled', node)
    if (object.k === 'bottom') return BOTTOM
    if (object.k === 'void') return this.throwsOnUndefined(node)
    if (object.k === 'null') return this.throwsOnNull(node)

    if (name === 'length' && object.k === 'array')
      return scalar(ir.lit(BigInt(object.items.length)), true)

    if (name === 'length' && object.k === 'list') return scalar(ir.listLen(object.e), true)

    if (name === 'length' && object.k === 'scalar' && object.e.ty === 'str') {
      return scalar(ir.strLen(object.e), true)
    }

    if (object.k === 'map' || object.k === 'set') {
      if (name === 'size') return this.collectionSize(object, node)
      throw new Unsupported(`reading \`.${name}\` of ${describe(object)} is not supported`, node)
    }

    if (object.k !== 'record')
      throw new Unsupported(`reading \`.${name}\` of ${describe(object)} is not supported`, node)

    return object.fields.get(name) ?? this.absent(name, node)
  }

  private allowsUndefined(node: N): boolean {
    const allows = (type: Type): boolean =>
      (type.flags & (TypeFlags.Undefined | TypeFlags.Any | TypeFlags.Unknown)) !== 0 ||
      (type.isUnionType() && type.getTypes().some(allows))

    const type = this.checker.getTypeAtLocation(node)
    return !!type && allows(type)
  }

  private indexArray(
    items: Value[],
    indexExpr: Expr,
    node: N,
    wrapNegative: boolean,
    refusal: () => Unsupported,
  ): Value {
    const settled = this.instance?.fixed.size
      ? ir.substitute(indexExpr, this.instance.fixed)
      : indexExpr

    if (settled.t === 'lit') {
      const raw = Number(settled.value as bigint)
      const pos = wrapNegative && raw < 0 ? items.length + raw : raw
      return items[pos] ?? this.absent(undefined, node)
    }

    if (items.length === 0) return this.absent(undefined, node)

    if (items.length <= 64) {
      const idx = wrapNegative
        ? ir.ite(ir.lt(settled, ir.lit(0n)), ir.add(ir.lit(BigInt(items.length)), settled), settled)
        : settled
      const free = ir.freeVariables(settled)
      const canSplit =
        this.instance?.binders.some((b) => free.has(b.name) && b.domain && b.domain.length > 1) ??
        false
      const hasMutable = items.some(
        (item) => (item.k === 'record' || item.k === 'array') && item.own?.epoch === this.epoch,
      )

      if (!(hasMutable && canSplit)) {
        const binder =
          settled.t === 'var'
            ? this.instance?.binders.find((b) => b.name === settled.name)
            : undefined

        const inBounds = (v: bigint) =>
          (wrapNegative ? v >= -BigInt(items.length) : v >= 0n) && v < BigInt(items.length)

        const guaranteed =
          !!binder &&
          ((binder.domain !== undefined &&
            binder.domain.length > 0 &&
            binder.domain.every((v) => typeof v === 'bigint' && inBounds(v))) ||
            (binder.range !== undefined && inBounds(binder.range[0]) && inBounds(binder.range[1])))

        if (guaranteed) {
          let acc = items[items.length - 1]!

          for (let k = items.length - 2; k >= 0; k--)
            acc = this.merge(ir.eq(idx, ir.lit(BigInt(k))), items[k]!, acc)

          return acc
        }

        if (this.allowsUndefined(node)) {
          let acc: Value = this.absent(undefined, node)

          for (let k = items.length - 1; k >= 0; k--)
            acc = this.merge(ir.eq(idx, ir.lit(BigInt(k))), items[k]!, acc)

          return acc
        }

        if (!canSplit) {
          const pick = (k: number): Value => {
            if (k === items.length) {
              this.emit('missing', ir.FALSE, node)
              return BOTTOM
            }

            return this.branch(
              ir.eq(idx, ir.lit(BigInt(k))),
              () => items[k]!,
              () => pick(k + 1),
            )
          }

          return pick(0)
        }
      }
    }

    const raw = Number(this.settle(indexExpr, refusal).value as bigint)
    const pos = wrapNegative && raw < 0 ? items.length + raw : raw
    return items[pos] ?? this.absent(undefined, node)
  }

  private element(object: Value, node: N, env: Env): Value {
    const index = node.argumentExpression
    if (object.k === 'bottom') return BOTTOM
    const keyVal = this.evalExpr(index, env)
    if (keyVal.k === 'bottom') return BOTTOM
    if (object.k === 'void') return this.throwsOnUndefined(node)
    if (object.k === 'null') return this.throwsOnNull(node)

    if (object.k === 'array') {
      const refusal = () =>
        new Unsupported('an array can only be indexed by a position that is known here', node)

      if (!isNumber(keyVal) || keyVal.k !== 'scalar') throw refusal()
      return this.indexArray(object.items, keyVal.e, node, false, refusal)
    }

    if (object.k === 'list') {
      const refusal = () =>
        new Unsupported('an arbitrary-length array can only be indexed at position 0', node)

      if (!isNumber(keyVal) || keyVal.k !== 'scalar') throw refusal()
      const pos = this.settle(keyVal.e, refusal).value as bigint
      if (pos !== 0n) throw refusal()
      const nonEmpty = ir.lt(ir.lit(0n), ir.listLen(object.e))
      const head = scalar(ir.listHead(object.e), object.num)

      if (this.allowsUndefined(node))
        return this.merge(nonEmpty, head, this.absent(undefined, node))

      this.emit('missing', nonEmpty, node)
      return head
    }

    if (object.k !== 'record')
      throw new Unsupported(`indexing ${describe(object)} is not supported`, node)

    return this.over(keyVal, (k) => {
      if (k.k === 'bottom') return BOTTOM

      if (k.k !== 'scalar' || (k.e.ty !== 'str' && k.e.ty !== 'int')) {
        throw new Unsupported(`indexing an object with ${describe(k)} is not supported`, index)
      }

      if (k.e.t === 'lit') {
        const name = String(k.e.value)
        return object.fields.get(name) ?? this.absent(name, node)
      }

      const intKey = k.e.ty === 'int'
      const key = k.e
      const names = intKey
        ? [...object.fields.keys()].filter((name) => /^(0|-?[1-9]\d*)$/.test(name))
        : [...object.fields.keys()]

      const pick = (i: number): Value => {
        if (i === names.length) {
          if (!this.allowsUndefined(node)) {
            this.emit('missing', ir.FALSE, node)
            return BOTTOM
          }

          if (!intKey) {
            const inherited = Object.getOwnPropertyNames(Object.prototype).filter(
              (name) => !object.fields.has(name),
            )
            this.emit(
              'inherited',
              ir.not(inherited.map((name) => ir.eq(key, ir.lit(name))).reduce(ir.or, ir.FALSE)),
              node,
            )
          }

          return this.absent(undefined, node)
        }

        const match = intKey ? ir.eq(key, ir.lit(BigInt(names[i]!))) : ir.eq(key, ir.lit(names[i]!))
        return this.branch(
          match,
          () => object.fields.get(names[i]!)!,
          () => pick(i + 1),
        )
      }

      return pick(0)
    })
  }

  private chain(node: N, env: Env, then: (value: Value) => Value): Value {
    if (node.kind === K.NonNullExpression) return this.chain(node.expression, env, then)
    if (!inOptionalChain(node)) return then(this.evalExpr(node, env))

    const access = (link: N, object: Value) =>
      link.kind === K.PropertyAccessExpression
        ? this.property(object, link)
        : this.element(object, link, env)

    if (node.kind === K.CallExpression) {
      const callee = node.expression

      if (callee.kind === K.PropertyAccessExpression || callee.kind === K.ElementAccessExpression) {
        return this.chain(callee.expression, env, (holder) =>
          this.over(holder, (receiver) => {
            if (receiver.k === 'bottom') return BOTTOM

            if (callee.questionDotToken && (receiver.k === 'void' || receiver.k === 'null'))
              return VOID

            if (!node.questionDotToken) {
              if (callee.kind !== K.PropertyAccessExpression)
                throw new Unsupported('calling a method by a computed name is not supported', node)

              return then(this.method(receiver, node, env))
            }

            return this.over(access(callee, receiver), (fn) =>
              fn.k === 'bottom'
                ? BOTTOM
                : fn.k === 'void' || fn.k === 'null'
                  ? VOID
                  : then(this.call(fn, this.arguments(node, env), node)),
            )
          }),
        )
      }

      return this.chain(callee, env, (called) =>
        this.over(called, (fn) =>
          fn.k === 'bottom'
            ? BOTTOM
            : (fn.k === 'void' || fn.k === 'null') && node.questionDotToken
              ? VOID
              : then(this.call(fn, this.arguments(node, env), node)),
        ),
      )
    }

    return this.chain(node.expression, env, (holder) =>
      this.over(holder, (object) => {
        if (object.k === 'bottom') return BOTTOM
        if (node.questionDotToken && (object.k === 'void' || object.k === 'null')) return VOID
        return then(access(node, object))
      }),
    )
  }

  private arguments(node: N, env: Env): Value[] {
    const out: Value[] = []

    for (const argument of node.arguments as N[]) {
      if (argument.kind === K.SpreadElement) {
        const list = this.settled(
          this.copied(
            this.evalExpr(argument.expression, env),
            argument,
            'cannot spread',
            'as call arguments',
          ),
        )

        if (list.k !== 'array')
          throw new Unsupported(
            'spread arguments require a list whose length is known here',
            argument,
          )

        out.push(...list.items)
      } else out.push(this.evalExpr(argument, env))
    }

    return out
  }

  private callExpression(node: N, env: Env): Value {
    const callee = node.expression
    const args = () => this.arguments(node, env)

    if (callee.kind === K.Identifier && !env.get(callee.text) && this.isBuiltin(callee)) {
      if (
        callee.text === 'Boolean' ||
        callee.text === 'String' ||
        callee.text === 'Number' ||
        callee.text === 'BigInt'
      ) {
        this.assertBuiltinsIntact(node)
        const evaluated = args()
        if (evaluated.some((v) => v.k === 'bottom')) return BOTTOM

        if (callee.text === 'Boolean') {
          return evaluated.length === 0
            ? scalar(ir.FALSE)
            : scalar(this.truthy(evaluated[0]!, node))
        }

        if (callee.text === 'String') {
          return evaluated.length === 0 ? scalar(ir.lit('')) : this.text(evaluated[0]!, node, true)
        }

        if (callee.text === 'Number') {
          if (evaluated.length === 0) return scalar(ir.lit(0n), true)
          return this.over(evaluated[0]!, (value) => {
            if (value.k === 'bottom') return BOTTOM

            if (
              value.k === 'rat' ||
              value.k === 'quot' ||
              value.k === 'float' ||
              value.k === 'infinite'
            )
              return value

            const integer = this.scalarOf(value, node, 'int')
            if (!isNumber(value)) this.emit('overflow', ir.isSafe(integer), node)
            return scalar(integer, true)
          })
        }

        if (evaluated.length === 0) throw new Unsupported('`BigInt` requires an argument', node)
        return this.over(evaluated[0]!, (value) => {
          if (value.k === 'bottom') return BOTTOM
          return scalar(this.scalarOf(value, node, 'int'), false)
        })
      }
    }

    if (
      callee.kind === K.PropertyAccessExpression &&
      callee.expression.kind === K.Identifier &&
      !env.get(callee.expression.text) &&
      this.isBuiltin(callee.expression)
    ) {
      const host = callee.expression.text as string
      const name = callee.name.text as string
      if (host === 'Math') return this.math(name, node, env)
      if (host === 'Array' && name === 'from') return this.arrayFrom(args(), node)

      if (host === 'Array' && name === 'isArray') {
        this.assertBuiltinsIntact(node)
        const [first] = args()
        return this.over(first ?? VOID, (v) =>
          v.k === 'bottom' ? BOTTOM : scalar(ir.lit(v.k === 'array' || v.k === 'list')),
        )
      }

      if (
        host === 'Number' &&
        (name === 'isInteger' ||
          name === 'isFinite' ||
          name === 'isNaN' ||
          name === 'isSafeInteger')
      ) {
        this.assertBuiltinsIntact(node)
        const [first] = args()
        return this.over(first ?? VOID, (v) => {
          if (v.k === 'bottom') return BOTTOM
          if (name === 'isNaN') return scalar(ir.FALSE)
          if (name === 'isFinite') return scalar(ir.lit(isNumeric(v)))

          if (v.k === 'rat')
            return scalar(ir.eq(ir.mod(v.num, ir.lit(2n ** BigInt(v.shift))), ir.lit(0n)))

          if (v.k === 'quot') return scalar(ir.eq(ir.mod(v.num, v.den), ir.lit(0n)))

          if (v.k === 'float')
            return scalar(
              ir.lit(
                name === 'isInteger' ? Number.isInteger(v.value) : Number.isSafeInteger(v.value),
              ),
            )

          return scalar(ir.lit(isNumber(v)))
        })
      }

      if (
        host === 'Object' &&
        (name === 'keys' ||
          name === 'values' ||
          name === 'entries' ||
          name === 'hasOwn' ||
          name === 'fromEntries' ||
          name === 'freeze' ||
          name === 'assign')
      ) {
        return this.objectStatic(name, args(), node)
      }
    }

    if (callee.kind === K.PropertyAccessExpression && !this.isNamespace(callee.expression, env)) {
      return this.over(this.evalExpr(callee.expression, env), (receiver) =>
        this.method(receiver, node, env),
      )
    }

    return this.call(this.evalExpr(callee, env), args(), node)
  }

  private objectStatic(name: string, args: Value[], node: N): Value {
    this.assertBuiltinsIntact(node)

    if (name === 'freeze') {
      if (args.length > 1) throw new Unsupported('`Object.freeze` takes one argument', node)
      return this.over(args[0] ?? VOID, (v) => {
        if (v.k === 'record' || v.k === 'array') {
          if (v.own?.epoch === this.epoch) this.writtenTo?.add(v)
          this.freeze(v)
        }

        return v
      })
    }

    if (name === 'assign') {
      if (args.length < 1) throw new Unsupported('`Object.assign` requires a target object', node)
      if (args.some((a) => a.k === 'bottom')) return BOTTOM
      const inlineTarget = node.arguments[0]?.kind === K.ObjectLiteralExpression
      return this.over(args[0]!, (target) => {
        if (target.k === 'bottom') return BOTTOM
        if (target.k === 'void') return this.throwsOnUndefined(node)
        if (target.k === 'null') return this.throwsOnNull(node)

        if (target.k !== 'record')
          throw new Unsupported(`\`Object.assign\` on ${describe(target)} is not supported`, node)

        if (inlineTarget) {
          const sources = args.slice(1)

          const spreadInto = (acc: Extract<Value, { k: 'record' }>, idx: number): Value => {
            if (idx === sources.length) return acc
            return this.over(sources[idx]!, (src) => {
              if (src.k === 'bottom') return BOTTOM
              if (src.k === 'void' || src.k === 'null') return spreadInto(acc, idx + 1)

              if (src.k !== 'record')
                throw new Unsupported(
                  `\`Object.assign\` from ${describe(src)} is not supported`,
                  node,
                )

              const next = new Map(acc.fields)

              for (const [k, v] of src.fields) {
                if (k === '__proto__')
                  throw new Unsupported(
                    'assigning `__proto__` via `Object.assign` is not modeled',
                    node,
                  )

                next.set(k, v)
              }

              const unordered = acc.unordered || (src.unordered && src.fields.size > 0)
              return spreadInto(
                this.fresh({
                  k: 'record',
                  fields: next,
                  ...(unordered ? { unordered: true } : {}),
                }),
                idx + 1,
              )
            })
          }

          return spreadInto(target, 0)
        }

        for (const source of args.slice(1)) {
          const applied = this.over(source, (src) => {
            if (src.k === 'bottom') return BOTTOM
            if (src.k === 'void' || src.k === 'null') return VOID

            if (src.k !== 'record')
              throw new Unsupported(
                `\`Object.assign\` from ${describe(src)} is not supported`,
                node,
              )

            for (const [k, v] of Array.from(src.fields)) {
              if (k === '__proto__')
                throw new Unsupported(
                  'assigning `__proto__` via `Object.assign` is not modeled',
                  node,
                )

              this.assertChangeable(target, v, node)
              this.write(target, k, v)
            }

            if (src.unordered && src.fields.size > 0) target.unordered = true
            return VOID
          })
          if (applied.k === 'bottom') return BOTTOM
        }

        return target
      })
    }

    if (name === 'hasOwn') {
      if (args.length < 2)
        throw new Unsupported('`Object.hasOwn` takes an object and a property name', node)

      return this.over(args[0]!, (obj) =>
        this.over(args[1]!, (keyVal) => {
          if (obj.k === 'bottom' || keyVal.k === 'bottom') return BOTTOM
          if (obj.k === 'void') return this.throwsOnUndefined(node)
          if (obj.k === 'null') return this.throwsOnNull(node)
          const key =
            keyVal.k === 'scalar' && keyVal.e.ty === 'str'
              ? keyVal.e
              : isNumber(keyVal) && keyVal.k === 'scalar'
                ? ir.toStr(keyVal.e)
                : undefined

          if (!key)
            throw new Unsupported(
              `\`Object.hasOwn\` expects a string or number key, but found ${describe(keyVal)}`,
              node,
            )

          if (obj.k === 'array') {
            const lit = this.settle(
              key,
              () => new Unsupported('`Object.hasOwn` on an array requires a known key', node),
            ).value as string
            return scalar(
              ir.lit(lit === 'length' || (isArrayIndexKey(lit) && Number(lit) < obj.items.length)),
            )
          }

          if (obj.k === 'list') {
            const lit = this.settle(
              key,
              () =>
                new Unsupported(
                  '`Object.hasOwn` on an arbitrary-length array requires a known key',
                  node,
                ),
            ).value as string
            if (lit === 'length') return scalar(ir.TRUE)

            if (isArrayIndexKey(lit))
              return scalar(ir.lt(ir.lit(BigInt(Number(lit))), ir.listLen(obj.e)))

            return scalar(ir.FALSE)
          }

          if (obj.k === 'scalar' && obj.e.ty === 'str') {
            const str = this.settle(
              obj.e,
              () =>
                new Unsupported('`Object.hasOwn` on a string requires a string known here', node),
            ).value as string
            const lit = this.settle(
              key,
              () => new Unsupported('`Object.hasOwn` on a string requires a known key', node),
            ).value as string
            return scalar(ir.lit(Object.hasOwn(str as unknown as object, lit)))
          }

          if (obj.k === 'closure')
            throw new Unsupported('`Object.hasOwn` on a function is not supported', node)

          if (obj.k !== 'record') return scalar(ir.FALSE)
          if (key.t === 'lit') return scalar(ir.lit(obj.fields.has(key.value as string)))
          return scalar(
            [...obj.fields.keys()].map((k) => ir.eq(key, ir.lit(k))).reduce(ir.or, ir.FALSE),
          )
        }),
      )
    }

    if (name === 'fromEntries') {
      if (args.length !== 1)
        throw new Unsupported('`Object.fromEntries` takes one list of entries', node)

      return this.over(args[0]!, (given) => {
        if (given.k === 'bottom') return BOTTOM
        const source = this.listed(given, node)

        if (source.k !== 'array')
          throw new Unsupported(
            `\`Object.fromEntries\` of ${describe(given)} is not supported`,
            node,
          )

        const fields = new Map<string, Value>()

        for (const item of source.items) {
          const pair = this.settled(item)

          if (pair.k !== 'array' || pair.items.length < 2)
            throw new Unsupported('`Object.fromEntries` needs a list of `[key, value]` pairs', node)

          const rawKey = this.settled(pair.items[0]!)
          const keyExpr =
            rawKey.k === 'scalar' && rawKey.e.ty === 'str'
              ? rawKey.e
              : isNumber(rawKey) && rawKey.k === 'scalar'
                ? ir.toStr(rawKey.e)
                : undefined

          if (!keyExpr)
            throw new Unsupported('`Object.fromEntries` requires string or number keys', node)

          const key = this.settle(
            keyExpr,
            () => new Unsupported('`Object.fromEntries` requires keys known here', node),
          ).value as string

          if (key === '__proto__')
            throw new Unsupported('`__proto__` in `Object.fromEntries` is not modeled', node)

          fields.set(key, pair.items[1]!)
        }

        return this.fresh({ k: 'record', fields })
      })
    }

    if (args.length !== 1) throw new Unsupported(`\`Object.${name}\` takes one argument`, node)
    return this.over(args[0]!, (obj) => {
      if (obj.k === 'bottom') return BOTTOM
      if (obj.k === 'void') return this.throwsOnUndefined(node)
      if (obj.k === 'null') return this.throwsOnNull(node)

      if (obj.k === 'array') {
        const items = obj.items.map((item, i) =>
          name === 'keys'
            ? scalar(ir.lit(String(i)))
            : name === 'values'
              ? item
              : this.fresh({ k: 'array', items: [scalar(ir.lit(String(i))), item] }),
        )
        return this.fresh({ k: 'array', items })
      }

      if (obj.k !== 'record')
        throw new Unsupported(`\`Object.${name}\` on ${describe(obj)} is not supported`, node)

      if (obj.unordered && obj.fields.size > 0) {
        throw new Unsupported(`\`Object.${name}\` on an input object is not supported`, node)
      }

      const keys = ownKeysOrdered(obj.fields)
      const items = keys.map((key) =>
        name === 'keys'
          ? scalar(ir.lit(key))
          : name === 'values'
            ? obj.fields.get(key)!
            : this.fresh({ k: 'array', items: [scalar(ir.lit(key)), obj.fields.get(key)!] }),
      )
      return this.fresh({ k: 'array', items })
    })
  }

  private method(receiver: Value, node: N, env: Env): Value {
    const method = node.expression.name.text as string
    const args = () => this.arguments(node, env)
    if (receiver.k === 'bottom') return BOTTOM
    if (receiver.k === 'void') return this.throwsOnUndefined(node)
    if (receiver.k === 'null') return this.throwsOnNull(node)

    if (
      (receiver.k === 'scalar' ||
        receiver.k === 'rat' ||
        receiver.k === 'quot' ||
        receiver.k === 'float') &&
      method === 'toString' &&
      node.arguments.length === 0
    ) {
      this.assertBuiltinsIntact(node)
      return this.text(receiver, node, false)
    }

    if (receiver.k === 'scalar' && receiver.e.ty === 'str') {
      if (method === 'padStart' || method === 'padEnd') {
        this.assertBuiltinsIntact(node)
        return this.pad(receiver.e, method === 'padStart', args(), node)
      }

      this.assertBuiltinsIntact(node)
      return this.stringMethod(receiver.e, method, args(), node)
    }

    if (receiver.k === 'array') {
      this.assertBuiltinsIntact(node)
      return this.arrayMethod(receiver, method, args(), node)
    }

    if (receiver.k === 'list') {
      this.assertBuiltinsIntact(node)
      return this.listMethod(receiver, method, args(), node)
    }

    if (receiver.k === 'map' || receiver.k === 'set') {
      this.assertBuiltinsIntact(node)
      return this.collectionMethod(receiver, method, args(), node)
    }

    if (receiver.k === 'record')
      return this.call(receiver.fields.get(method) ?? this.absent(method, node), args(), node)

    throw new Unsupported(`calling \`.${method}\` on ${describe(receiver)} is not supported`, node)
  }

  private assertBuiltinsIntact(use: Node) {
    if (this.tampering === null) {
      this.tampering = undefined
      const builtins = new Set([
        'Math',
        'Object',
        'Array',
        'String',
        'Number',
        'BigInt',
        'Boolean',
        'JSON',
        'Reflect',
        'Function',
        'Symbol',
        'Map',
        'Set',
        'globalThis',
        'Error',
        'TypeError',
        'RangeError',
        'ReferenceError',
        'SyntaxError',
        'URIError',
        'EvalError',
      ])

      const fromBuiltin = (node: N): boolean => {
        const root = rootOf(node)
        return root.kind === K.Identifier && (root.text === 'globalThis' || this.isBuiltin(root))
      }

      const prototype = (node: N): boolean =>
        (node.kind === K.PropertyAccessExpression &&
          (node.name.text === '__proto__' ||
            (node.name.text === 'prototype' && fromBuiltin(node.expression)))) ||
        (node.kind === K.ElementAccessExpression &&
          node.argumentExpression.kind === K.StringLiteral &&
          (node.argumentExpression.text === '__proto__' ||
            (node.argumentExpression.text === 'prototype' && fromBuiltin(node.expression)))) ||
        (node.kind === K.CallExpression &&
          /(^|\.)(Object|Reflect)\.getPrototypeOf$/.test(
            node.expression.getText(node.getSourceFile()),
          ))

      const throughPrototype = (node: N): boolean => {
        for (;;) {
          if (prototype(node)) return true

          if (
            node.kind !== K.PropertyAccessExpression &&
            node.kind !== K.ElementAccessExpression &&
            node.kind !== K.ParenthesizedExpression &&
            node.kind !== K.AsExpression &&
            node.kind !== K.NonNullExpression
          )
            return false

          node = node.expression
        }
      }

      const rootOf = (node: N): N => {
        while (
          node.kind === K.PropertyAccessExpression ||
          node.kind === K.ElementAccessExpression ||
          node.kind === K.ParenthesizedExpression ||
          node.kind === K.AsExpression ||
          node.kind === K.NonNullExpression
        )
          node = node.expression

        return node
      }

      const visit = (node: N) => {
        if (this.tampering) return
        const assigns =
          node.kind === K.BinaryExpression &&
          node.operatorToken.kind >= K.FirstAssignment &&
          node.operatorToken.kind <= K.LastAssignment
        const target = assigns
          ? node.left
          : node.kind === K.DeleteExpression
            ? node.expression
            : (node.kind === K.PrefixUnaryExpression || node.kind === K.PostfixUnaryExpression) &&
                (node.operator === K.PlusPlusToken || node.operator === K.MinusMinusToken)
              ? node.operand
              : undefined
        const root = target && target.kind !== K.Identifier ? rootOf(target) : undefined
        const writes =
          node.kind === K.CallExpression &&
          WRITERS.test(node.expression.getText(node.getSourceFile()))
        const handed = writes
          ? (node.arguments as N[])
              .slice(0, 1)
              .map(rootOf)
              .find((a) => a.kind === K.Identifier && builtins.has(a.text))
          : undefined
        const replaced =
          target?.kind === K.Identifier && builtins.has(target.text) ? target : undefined
        const culprit =
          root?.kind === K.Identifier && builtins.has(root.text) ? root : (replaced ?? handed)

        if (culprit && this.isBuiltin(culprit)) {
          const at = locate(node)
          this.tampering = {
            message: `\`${culprit.text}\` is modified at ${at.file}:${at.line}, so built-in behaviour cannot be assumed`,
            node,
          }
          return
        }

        let escapes = false

        if (prototype(node)) {
          let outer = node

          while (
            outer.parent.kind === K.ParenthesizedExpression ||
            outer.parent.kind === K.AsExpression ||
            outer.parent.kind === K.NonNullExpression
          )
            outer = outer.parent

          const parent = outer.parent
          const stored =
            ((parent.kind === K.VariableDeclaration || parent.kind === K.PropertyAssignment) &&
              parent.initializer === outer) ||
            (parent.kind === K.BinaryExpression &&
              parent.right === outer &&
              parent.operatorToken.kind >= K.FirstAssignment &&
              parent.operatorToken.kind <= K.LastAssignment) ||
            parent.kind === K.ArrayLiteralExpression ||
            parent.kind === K.SpreadElement ||
            parent.kind === K.SpreadAssignment ||
            parent.kind === K.ShorthandPropertyAssignment
          const passed =
            (parent.kind === K.CallExpression || parent.kind === K.NewExpression) &&
            parent.expression !== outer
          let method = parent
          const borrowed =
            (parent.kind === K.PropertyAccessExpression ||
              parent.kind === K.ElementAccessExpression) &&
            parent.expression === outer

          while (
            borrowed &&
            (method.parent.kind === K.ParenthesizedExpression ||
              method.parent.kind === K.AsExpression ||
              method.parent.kind === K.NonNullExpression)
          )
            method = method.parent

          const called =
            borrowed &&
            method.parent.kind === K.CallExpression &&
            method.parent.expression === method
          escapes = stored || passed || called
        }

        const named = node.kind === K.BindingElement ? (node.propertyName ?? node.name) : undefined
        const taken = named?.kind === K.ComputedPropertyName ? named.expression : named

        if (
          (taken?.kind === K.Identifier ||
            taken?.kind === K.StringLiteral ||
            taken?.kind === K.NoSubstitutionTemplateLiteral) &&
          (taken.text === 'prototype' || taken.text === '__proto__')
        ) {
          const whole = this.checker.getTypeAtLocation(node.parent)
          const property =
            whole && !(whole.flags & (TypeFlags.Any | TypeFlags.Unknown))
              ? this.checker.getPropertyOfType(whole, 'prototype')
              : undefined
          const declared = property?.declarations[0]?.resolve()
          let holder = node.parent

          while (
            holder.kind === K.ObjectBindingPattern ||
            holder.kind === K.ArrayBindingPattern ||
            holder.kind === K.BindingElement
          )
            holder = holder.parent

          if (
            taken.text === '__proto__' ||
            holder.kind === K.Parameter ||
            !declared ||
            this.program.isSourceFileDefaultLibrary(declared.getSourceFile())
          )
            escapes = true
        }

        if (
          escapes ||
          (target && target.kind !== K.Identifier && throughPrototype(target)) ||
          (writes && (node.arguments as N[]).slice(0, 1).some(throughPrototype))
        ) {
          const at = locate(node)
          this.tampering = {
            message: `a prototype is modified, stored or handed on at ${at.file}:${at.line}, so built-in behaviour cannot be assumed`,
            node,
          }
          return
        }

        node.forEachChild(visit)
      }

      for (const name of this.program.getSourceFileNames()) {
        const file = this.program.getSourceFile(name)

        if (file && !file.isDeclarationFile && !this.program.isSourceFileFromExternalLibrary(file))
          visit(file)
      }
    }

    if (this.tampering) throw new Unsupported(this.tampering.message, use)
  }

  private math(name: string, node: N, env: Env): Value {
    this.assertBuiltinsIntact(node)
    const parameters = node.arguments as N[]
    const [first] = parameters

    if (
      first &&
      parameters.length === 1 &&
      (name === 'floor' || name === 'trunc' || name === 'ceil' || name === 'round')
    ) {
      return this.over(this.evalExpr(first, env), (value) => {
        if (value.k === 'bottom') return BOTTOM
        if (isNumber(value)) return value

        if (value.k === 'rat') {
          const d = ir.lit(2n ** BigInt(value.shift))
          if (name === 'trunc') return scalar(ir.div(value.num, d), true)
          if (name === 'floor') return scalar(ir.fdiv(value.num, d), true)
          if (name === 'ceil') return scalar(ir.neg(ir.fdiv(ir.neg(value.num), d)), true)
          const half = ir.lit(2n ** BigInt(value.shift - 1))
          return scalar(ir.fdiv(ir.add(value.num, half), d), true)
        }

        if (value.k === 'quot') {
          const { num: a, den: b } = value

          if (name === 'round') {
            const limit = ir.lit(2n ** 52n)
            this.emit('round', ir.and(ir.lt(ir.neg(limit), a), ir.lt(a, limit)), first)
            return scalar(ir.fdiv(ir.add(ir.mul(ir.lit(2n), a), b), ir.mul(ir.lit(2n), b)), true)
          }

          if (name === 'trunc') return scalar(ir.div(a, b), true)
          return scalar(name === 'floor' ? ir.fdiv(a, b) : ir.neg(ir.fdiv(ir.neg(a), b)), true)
        }

        if (value.k === 'float') {
          const rounded =
            name === 'floor'
              ? Math.floor(value.value)
              : name === 'ceil'
                ? Math.ceil(value.value)
                : name === 'trunc'
                  ? Math.trunc(value.value)
                  : Math.round(value.value)
          return this.fromJsNumber(rounded, node)
        }

        throw new Unsupported(
          `Math.${name} is modeled for numbers, but this is ${describe(value)}`,
          first,
        )
      })
    }

    if (first && parameters.length === 1 && name === 'abs') {
      return this.over(this.evalExpr(first, env), (value) => {
        if (value.k === 'bottom') return BOTTOM
        if (value.k === 'infinite') return { k: 'infinite', negative: false }

        if (value.k === 'rat')
          return {
            k: 'rat',
            num: ir.ite(ir.lt(value.num, ir.lit(0n)), ir.neg(value.num), value.num),
            shift: value.shift,
          }

        if (value.k === 'quot') {
          const abs = (e: Expr) => ir.ite(ir.lt(e, ir.lit(0n)), ir.neg(e), e)
          return { k: 'quot', num: abs(value.num), den: abs(value.den) }
        }

        if (value.k === 'float') return this.fromJsNumber(Math.abs(value.value), node)

        if (!isNumber(value))
          throw new Unsupported(
            `Math.abs is modeled for numbers, but this is ${describe(value)}`,
            first,
          )

        const e = (value as { e: Expr }).e
        return scalar(ir.ite(ir.lt(e, ir.lit(0n)), ir.neg(e), e), true)
      })
    }

    if (first && parameters.length === 1 && name === 'sign') {
      return this.over(this.evalExpr(first, env), (value) => {
        if (value.k === 'bottom') return BOTTOM
        if (value.k === 'infinite') return scalar(ir.lit(value.negative ? -1n : 1n), true)

        if (value.k === 'rat')
          return scalar(
            ir.ite(
              ir.lt(value.num, ir.lit(0n)),
              ir.lit(-1n),
              ir.ite(ir.eq(value.num, ir.lit(0n)), ir.lit(0n), ir.lit(1n)),
            ),
            true,
          )

        if (value.k === 'quot') {
          const sameSign = ir.or(
            ir.and(ir.lt(ir.lit(0n), value.num), ir.lt(ir.lit(0n), value.den)),
            ir.and(ir.lt(value.num, ir.lit(0n)), ir.lt(value.den, ir.lit(0n))),
          )
          return scalar(
            ir.ite(
              ir.eq(value.num, ir.lit(0n)),
              ir.lit(0n),
              ir.ite(sameSign, ir.lit(1n), ir.lit(-1n)),
            ),
            true,
          )
        }

        if (value.k === 'float') return scalar(ir.lit(BigInt(Math.sign(value.value))), true)

        if (!isNumber(value))
          throw new Unsupported(
            `Math.sign is modeled for numbers, but this is ${describe(value)}`,
            first,
          )

        const e = (value as { e: Expr }).e
        return scalar(
          ir.ite(
            ir.lt(e, ir.lit(0n)),
            ir.lit(-1n),
            ir.ite(ir.eq(e, ir.lit(0n)), ir.lit(0n), ir.lit(1n)),
          ),
          true,
        )
      })
    }

    if (name === 'min' || name === 'max') {
      const evaluated = this.arguments(node, env)
      if (!evaluated.length) return { k: 'infinite', negative: name === 'max' }
      const wantMin = name === 'min'

      const checkArg = (v: Value): Value => {
        if (v.k === 'bottom') return BOTTOM
        if (isNumeric(v) || v.k === 'infinite') return v
        throw new Unsupported(
          `Math.${name} is modeled for numbers, but this is ${describe(v)}`,
          node,
        )
      }

      let best = this.over(evaluated[0]!, checkArg)

      for (let i = 1; i < evaluated.length; i++) {
        best = this.over(best, (a) =>
          this.over(evaluated[i]!, (raw) => {
            const b = checkArg(raw)
            if (a.k === 'bottom' || b.k === 'bottom') return BOTTOM
            if (a.k === 'infinite') return (wantMin ? a.negative : !a.negative) ? a : b
            if (b.k === 'infinite') return (wantMin ? b.negative : !b.negative) ? b : a
            const pickB = this.compareNumeric(
              wantMin ? K.LessThanToken : K.GreaterThanToken,
              b,
              a,
              node,
            )
            return this.merge(pickB, b, a)
          }),
        )
      }

      return best
    }

    if (name === 'pow') {
      const args = this.arguments(node, env)
      if (args.length !== 2) throw new Unsupported('Math.pow takes two arguments', node)
      return this.over(args[0]!, (a) =>
        this.over(args[1]!, (b) => {
          if (a.k === 'bottom' || b.k === 'bottom') return BOTTOM

          if (!isNumeric(a) || !isNumeric(b))
            throw new Unsupported('Math.pow is modeled for numbers', node)

          return this.arithmetic(K.AsteriskAsteriskToken, a, b, node)
        }),
      )
    }

    throw new Unsupported(`Math.${name} is not supported`, node)
  }

  private text(value: Value, at: N, allowNullish = false): Value {
    return this.over(value, (part) => {
      if (part.k === 'bottom') return BOTTOM
      if (part.k === 'scalar' && part.e.ty === 'str') return part
      if (part.k === 'scalar' && part.e.ty === 'int') return scalar(ir.toStr(part.e))

      if (part.k === 'scalar' && part.e.ty === 'bool')
        return scalar(ir.ite(part.e, ir.lit('true'), ir.lit('false')))

      if (part.k === 'float') return scalar(ir.lit(String(part.value)))

      if (part.k === 'rat' || part.k === 'quot') {
        const known = this.settleNumber(
          part,
          () =>
            new Unsupported(
              'converting a fractional number to a string is not supported unless its value is known here',
              at,
            ),
        )
        return scalar(ir.lit(String(known)))
      }

      if (allowNullish && part.k === 'void') return scalar(ir.lit('undefined'))
      if (allowNullish && part.k === 'null') return scalar(ir.lit('null'))
      throw new Unsupported(`converting ${describe(part)} to a string is not supported`, at)
    })
  }

  private stringMethod(text: Expr, method: string, args: Value[], node: N): Value {
    const SUPPORTED = new Set([
      'slice',
      'substring',
      'charAt',
      'at',
      'codePointAt',
      'indexOf',
      'lastIndexOf',
      'startsWith',
      'endsWith',
      'includes',
      'trim',
      'trimStart',
      'trimEnd',
      'toUpperCase',
      'toLowerCase',
      'repeat',
      'split',
      'replace',
      'replaceAll',
    ])

    if (!SUPPORTED.has(method))
      throw new Unsupported(`calling \`.${method}\` on a string is not supported`, node)

    const knownStr = (v: Value | undefined, what: string): string => {
      const s = v ? this.settled(v) : VOID

      if (s.k !== 'scalar' || s.e.ty !== 'str')
        throw new Unsupported(`\`.${method}\` expects a string ${what}`, node)

      return this.settle(
        s.e,
        () => new Unsupported(`\`.${method}\` requires a ${what} known here`, node),
      ).value as string
    }

    const knownOptNum = (v: Value | undefined, what: string): number | undefined => {
      if (!v || v.k === 'void') return undefined
      const s = this.settled(v)

      if (!isNumber(s) || s.k !== 'scalar')
        throw new Unsupported(`\`.${method}\` expects a number ${what}`, node)

      return Number(
        this.settle(
          s.e,
          () => new Unsupported(`\`.${method}\` requires a ${what} known here`, node),
        ).value,
      )
    }

    if (
      (method === 'startsWith' || method === 'endsWith' || method === 'includes') &&
      text.t !== 'lit'
    ) {
      const noPos =
        args.length === 1 ||
        (args.length === 2 &&
          (args[1]!.k === 'void' ||
            (method !== 'endsWith' &&
              isNumber(args[1]!) &&
              args[1]!.k === 'scalar' &&
              args[1]!.e.t === 'lit' &&
              args[1]!.e.value === 0n)))

      if (noPos && args[0]) {
        const needleVal = this.settled(args[0])

        if (needleVal.k === 'scalar' && needleVal.e.ty === 'str') {
          if (method === 'startsWith') return scalar(ir.startsWith(text, needleVal.e))
          if (method === 'endsWith') return scalar(ir.endsWith(text, needleVal.e))
          return scalar(ir.includes(text, needleVal.e))
        }
      }
    }

    if (method === 'slice' && text.t !== 'lit') {
      const start = knownOptNum(args[0], 'start')
      const end = knownOptNum(args[1], 'end')
      if ((start === undefined || start === 0) && end === undefined) return scalar(text)
      const parts: Expr[] = []

      const flatten = (e: Expr) => {
        if (e.t === 'op' && e.op === 'concat') e.args.forEach(flatten)
        else parts.push(e)
      }

      flatten(text)

      if (parts[0]?.t === 'lit') {
        const head = parts[0].value as string
        const rest = parts.slice(1).reduce(ir.concat, ir.lit(''))

        if (start !== undefined && start >= 0 && start <= head.length && end === undefined) {
          const piece = head.slice(start)
          if (piece.isWellFormed()) return scalar(ir.concat(ir.lit(piece), rest))
        }

        if (
          start !== undefined &&
          end !== undefined &&
          start >= 0 &&
          end >= start &&
          end <= head.length
        ) {
          const piece = head.slice(start, end)
          if (piece.isWellFormed()) return scalar(ir.lit(piece))
        }
      }

      const last = parts.at(-1)

      if (last?.t === 'lit') {
        const tail = last.value as string
        const init = parts.slice(0, -1).reduce(ir.concat, ir.lit(''))

        if (
          (start === undefined || start === 0) &&
          end !== undefined &&
          end < 0 &&
          -end <= tail.length
        ) {
          const piece = tail.slice(0, end)
          if (piece.isWellFormed()) return scalar(ir.concat(init, ir.lit(piece)))
        }

        if (start !== undefined && start < 0 && -start <= tail.length && end === undefined) {
          const piece = tail.slice(start)
          if (piece.isWellFormed()) return scalar(ir.lit(piece))
        }
      }
    }

    const str = this.settle(
      text,
      () =>
        new Unsupported(
          `calling \`.${method}\` on a string whose value is not known here is not supported`,
          node,
        ),
    ).value as string

    switch (method) {
      case 'trim':
        return scalar(ir.lit(str.trim()))
      case 'trimStart':
        return scalar(ir.lit(str.trimStart()))
      case 'trimEnd':
        return scalar(ir.lit(str.trimEnd()))
      case 'toUpperCase':
        return scalar(ir.lit(this.wellFormed(str.toUpperCase(), node)))
      case 'toLowerCase':
        return scalar(ir.lit(this.wellFormed(str.toLowerCase(), node)))
      case 'slice': {
        const start = knownOptNum(args[0], 'start')
        const end = knownOptNum(args[1], 'end')
        return scalar(ir.lit(this.wellFormed(str.slice(start, end), node)))
      }
      case 'substring': {
        const start = knownOptNum(args[0], 'start') ?? 0
        const end = knownOptNum(args[1], 'end')
        return scalar(ir.lit(this.wellFormed(str.substring(start, end), node)))
      }
      case 'charAt': {
        const index = knownOptNum(args[0], 'index') ?? 0
        return scalar(ir.lit(this.wellFormed(str.charAt(index), node)))
      }
      case 'at': {
        const index = knownOptNum(args[0], 'index') ?? 0
        const ch = str.at(index)
        return ch === undefined ? VOID : scalar(ir.lit(this.wellFormed(ch, node)))
      }
      case 'codePointAt': {
        const index = knownOptNum(args[0], 'index') ?? 0
        const cp = str.codePointAt(index)
        return cp === undefined ? VOID : scalar(ir.lit(BigInt(cp)), true)
      }
      case 'indexOf': {
        const search = knownStr(args[0], 'search value')
        const from = knownOptNum(args[1], 'start position')
        return scalar(ir.lit(BigInt(str.indexOf(search, from))), true)
      }
      case 'lastIndexOf': {
        const search = knownStr(args[0], 'search value')
        const from = knownOptNum(args[1], 'start position')
        return scalar(
          ir.lit(
            BigInt(from === undefined ? str.lastIndexOf(search) : str.lastIndexOf(search, from)),
          ),
          true,
        )
      }
      case 'startsWith': {
        const search = knownStr(args[0], 'prefix')
        const pos = knownOptNum(args[1], 'position')
        return scalar(ir.lit(str.startsWith(search, pos)))
      }
      case 'endsWith': {
        const search = knownStr(args[0], 'suffix')
        const endPos = knownOptNum(args[1], 'end position')
        return scalar(ir.lit(str.endsWith(search, endPos)))
      }
      case 'includes': {
        const search = knownStr(args[0], 'substring')
        const pos = knownOptNum(args[1], 'position')
        return scalar(ir.lit(str.includes(search, pos)))
      }
      case 'repeat': {
        const count = knownOptNum(args[0], 'count') ?? 0

        if (count < 0) {
          this.emit('unreachable', ir.FALSE, node)
          return BOTTOM
        }

        if (count * str.length > 500)
          throw new Unsupported('`.repeat` produces a string too long to model', node)

        return scalar(ir.lit(str.repeat(count)))
      }
      case 'split': {
        const limit = knownOptNum(args[1], 'limit')
        const sepArg = args[0] ? this.settled(args[0]) : VOID
        const sep = sepArg.k === 'void' ? undefined : knownStr(sepArg, 'separator')
        const pieces = str.split(sep as unknown as string, limit)
        return this.fresh({
          k: 'array',
          items: pieces.map((p) => scalar(ir.lit(this.wellFormed(p, node)))),
        })
      }
      case 'replace':
      case 'replaceAll': {
        const search = knownStr(args[0], 'search value')
        const repl = knownStr(args[1], 'replacement')

        if (str.length > 500 || repl.length > 500)
          throw new Unsupported(`\`.${method}\` produces a string too long to model`, node)

        if (method === 'replaceAll') {
          const matches = search === '' ? str.length + 1 : str.split(search).length - 1
          const perMatch = repl.includes('$') ? repl.length + str.length : repl.length

          if (str.length + matches * perMatch > 500)
            throw new Unsupported('`.replaceAll` produces a string too long to model', node)
        }

        const out = method === 'replace' ? str.replace(search, repl) : str.replaceAll(search, repl)

        if (out.length > 500)
          throw new Unsupported(`\`.${method}\` produces a string too long to model`, node)

        return scalar(ir.lit(this.wellFormed(out, node)))
      }
      default:
        throw new Unsupported(`calling \`.${method}\` on a string is not supported`, node)
    }
  }

  private pad(text: Expr, atStart: boolean, args: Value[], node: N): Value {
    const [target, filler] = args

    const refusal = () =>
      new Unsupported('padding is modeled to a length that is known here, of at most 32', node)

    if (!target || args.length > 2 || !isNumber(target) || target.k !== 'scalar') throw refusal()
    const length = Number(this.settle(target.e, refusal).value)
    if (length > 32) throw refusal()
    let fill = ' '

    if (filler && filler.k !== 'void') {
      const refusalFill = () =>
        new Unsupported(
          'padding is modeled with a string known here, made of characters that are one UTF-16 unit each',
          node,
        )

      const f = this.settled(filler)
      if (f.k !== 'scalar' || f.e.ty !== 'str') throw refusalFill()
      const given = this.settle(f.e, refusalFill).value as string
      if ([...given].some((char) => char.length > 1)) throw refusalFill()
      fill = given
    }

    const padded = (missing: number, inner: Expr) => {
      if (missing <= 0 || fill === '') return inner
      const added = ir.lit(fill.repeat(Math.ceil(missing / fill.length)).slice(0, missing))
      return atStart ? ir.concat(added, inner) : ir.concat(inner, added)
    }

    if (text.t === 'lit') return scalar(padded(length - (text.value as string).length, text))

    if (text.t === 'op' && text.op === 'str') {
      const [number] = text.args as [Expr]
      let result: Expr = text

      for (let size = length - 1; size >= 1; size--) {
        const low = size === 1 ? 0n : 10n ** BigInt(size - 1)
        const positive = ir.and(
          ir.le(ir.lit(low), number),
          ir.lt(number, ir.lit(10n ** BigInt(size))),
        )
        const negative =
          size === 1
            ? ir.FALSE
            : ir.and(
                ir.lt(ir.lit(-(10n ** BigInt(size - 1))), number),
                ir.le(number, ir.lit(-(10n ** BigInt(size - 2)))),
              )
        result = ir.ite(ir.or(positive, negative), padded(length - size, text), result)
      }

      return scalar(result)
    }

    const len = ir.strLen(text)
    let result: Expr = text

    for (let size = length - 1; size >= 0; size--) {
      result = ir.ite(ir.eq(len, ir.lit(BigInt(size))), padded(length - size, text), result)
    }

    return scalar(result)
  }

  private isBuiltin(node: N): boolean {
    const declaration = this.checker.getSymbolAtLocation(node)?.declarations[0]?.resolve()
    return !!declaration && this.program.isSourceFileDefaultLibrary(declaration.getSourceFile())
  }

  private foldListForOf(
    list: Extract<Value, { k: 'list' }>,
    pattern: N,
    reassignable: boolean,
    body: N,
    env: Env,
    statement: N,
  ) {
    if (canExit(body))
      throw new Unsupported(
        'leaving a `for...of` loop over an arbitrary-length array early is not supported',
        statement,
      )

    if (pattern.kind !== K.Identifier)
      throw new Unsupported(
        'destructuring in a `for...of` loop over an arbitrary-length array is not supported',
        statement,
      )

    const bodyAssigned = new Set<string>()

    const scanAssign = (n: N) => {
      if (
        n.kind === K.ArrowFunction ||
        n.kind === K.FunctionExpression ||
        n.kind === K.FunctionDeclaration
      )
        return

      if (
        n.kind === K.BinaryExpression &&
        n.operatorToken.kind >= K.FirstAssignment &&
        n.operatorToken.kind <= K.LastAssignment
      )
        collectNames(n.left, bodyAssigned)

      if (
        (n.kind === K.PrefixUnaryExpression || n.kind === K.PostfixUnaryExpression) &&
        (n.operator === K.PlusPlusToken || n.operator === K.MinusMinusToken)
      )
        collectNames(n.operand, bodyAssigned)

      n.forEachChild(scanAssign)
    }

    scanAssign(body)
    const outerCells = [
      ...new Set(
        [...bodyAssigned]
          .map((n) => env.cell(n))
          .filter((c): c is Cell => !!c && this.cells.includes(c)),
      ),
    ]

    if (outerCells.length > 1)
      throw new Unsupported(
        'a `for...of` loop over an arbitrary-length array may update at most one outer variable',
        statement,
      )

    const elemTy = ir.elemTyOf(list.e.ty as ir.ListTy)
    const elName = `_el${this.lambdaCounter++}`
    const accCell = outerCells[0]
    const initIr = accCell ? this.irArgOf(accCell.value) : undefined

    if (accCell && !initIr)
      throw new Unsupported(
        'a `for...of` loop over an arbitrary-length array requires a boolean, bigint, number, string or array accumulator',
        statement,
      )

    const accName = accCell ? `_acc${this.lambdaCounter++}` : undefined
    const savedVal = accCell?.value
    const objects = objectsCreated
    const existingCells = new Set(this.cells)
    const outerAssigned = this.assignedTo
    const outerWritten = this.writtenTo
    const assigned = (this.assignedTo = new Set())
    const written = (this.writtenTo = new Set())
    const startObs = this.instance?.obligations.length ?? 0
    const savedPc = this.pc
    const savedCells = this.cells.length
    this.pc = []

    if (accCell && initIr && accName)
      accCell.value = this.valueFromExpr(ir.variable(accName, initIr.ty), initIr.num)

    try {
      const scope = env.child()
      const elCell = scope.set(
        pattern.text,
        scalar(ir.variable(elName, elemTy), list.num),
        reassignable,
      )
      if (elCell.mutable) this.cells.push(elCell)
      this.block(body.kind === K.Block ? body.statements : [body], scope.child(), {
        next: () => VOID,
      })
    } catch (error) {
      if (accCell && savedVal) accCell.value = savedVal
      throw error
    } finally {
      this.cells.length = savedCells
      this.pc = savedPc
      this.assignedTo = outerAssigned
      this.writtenTo = outerWritten
      if (outerWritten) for (const t of written) outerWritten.add(t)
    }

    for (const target of written) {
      if (target.own && target.own.born < objects) {
        if (accCell && savedVal) accCell.value = savedVal
        throw new Unsupported(
          'a `for...of` loop over an arbitrary-length array cannot mutate an outer object',
          statement,
        )
      }
    }

    for (const cell of assigned) {
      if (cell !== accCell && existingCells.has(cell)) {
        if (accCell && savedVal) accCell.value = savedVal
        throw new Unsupported(
          'a `for...of` loop over an arbitrary-length array may update at most one outer variable',
          statement,
        )
      }
    }

    if (accCell && outerAssigned) outerAssigned.add(accCell)
    const addedObs = this.instance ? this.instance.obligations.splice(startObs) : []

    for (const o of addedObs) {
      if (o.kind === 'expect') {
        if (accCell && savedVal) accCell.value = savedVal
        throw new Unsupported(
          'calling `expect()` inside a `for...of` loop over an arbitrary-length array is not supported',
          statement,
        )
      }

      if (
        accName &&
        (ir.freeVariables(o.guard).has(accName) || ir.freeVariables(o.claim).has(accName))
      ) {
        if (accCell && savedVal) accCell.value = savedVal
        throw new Unsupported(
          'a `for...of` loop over an arbitrary-length array whose body can throw or overflow depending on the accumulator is not supported',
          statement,
        )
      }

      const perElem = ir.or(ir.not(o.guard), o.claim)
      const allClaim = ir.listAll(list.e, elName, perElem)

      if (this.instance) {
        const guard = ir.all(this.pc)

        if (
          !(guard.t === 'lit' && guard.value === false) &&
          !(allClaim.t === 'lit' && allClaim.value === true)
        ) {
          this.instance.obligations.push({ ...o, guard, claim: allClaim })
        }
      }
    }

    if (accCell && initIr && accName) {
      const stepIr = this.irArgOf(accCell.value, initIr.ty, !!initIr.num)

      if (!stepIr) {
        accCell.value = savedVal!
        throw new Unsupported(
          'the accumulator of a `for...of` loop over an arbitrary-length array must keep the same type',
          statement,
        )
      }

      accCell.value = this.valueFromExpr(
        ir.listFold(list.e, initIr.e, accName, elName, stepIr.e),
        initIr.num,
      )
    }
  }

  private listMethod(
    list: Extract<Value, { k: 'list' }>,
    method: string,
    args: Value[],
    node: N,
  ): Value {
    const elemTy = ir.elemTyOf(list.e.ty as ir.ListTy)

    if (method === 'toReversed') {
      if (args.length !== 0) throw new Unsupported('`.toReversed` takes no arguments', node)
      return { k: 'list', e: ir.listReverse(list.e), ...(list.num ? { num: true } : {}) }
    }

    if (method === 'includes') {
      if (args.length !== 1)
        throw new Unsupported('`.includes` on an arbitrary-length array takes one argument', node)

      return this.over(args[0]!, (needle) => {
        if (needle.k === 'bottom') return BOTTOM

        if (needle.k === 'scalar' && needle.e.ty === elemTy && !!needle.num === !!list.num) {
          return scalar(ir.listElem(list.e, needle.e))
        }

        if (list.num) {
          if (needle.k === 'rat') {
            const scale = 1n << BigInt(needle.shift)
            return scalar(
              ir.and(
                ir.eq(ir.mod(needle.num, ir.lit(scale)), ir.lit(0n)),
                ir.listElem(list.e, ir.div(needle.num, ir.lit(scale))),
              ),
            )
          }

          if (needle.k === 'quot') {
            return scalar(
              ir.and(
                ir.eq(ir.mod(needle.num, needle.den), ir.lit(0n)),
                ir.listElem(list.e, ir.div(needle.num, needle.den)),
              ),
            )
          }

          if (needle.k === 'float') {
            return scalar(
              Number.isSafeInteger(needle.value)
                ? ir.listElem(list.e, ir.lit(BigInt(needle.value)))
                : ir.FALSE,
            )
          }
        }

        if (this.isPlain(needle)) return scalar(ir.FALSE)
        throw new Unsupported(
          `\`.includes\` on an arbitrary-length array is not supported with ${describe(needle)}`,
          node,
        )
      })
    }

    if (method === 'concat') {
      const join = (index: number, acc: Expr): Value => {
        if (index === args.length) return { k: 'list', e: acc, ...(list.num ? { num: true } : {}) }
        return this.over(args[index]!, (arg) => {
          if (arg.k === 'bottom') return BOTTOM
          const asList = this.asListExpr(arg, list.e.ty as ir.ListTy, !!list.num)
          if (asList) return join(index + 1, ir.listConcat(acc, asList.e))

          if (arg.k === 'scalar' && arg.e.ty === elemTy && !!arg.num === !!list.num) {
            return join(index + 1, ir.listConcat(acc, ir.listLit(list.e.ty as ir.ListTy, [arg.e])))
          }

          throw new Unsupported(
            `\`.concat\` on an arbitrary-length array cannot append ${describe(arg)}`,
            node,
          )
        })
      }

      return join(0, list.e)
    }

    if (method === 'slice') {
      if (args.length > 2) throw new Unsupported('`.slice` takes at most two arguments', node)
      const [startArg, endArg] = args

      if (endArg && endArg.k !== 'void')
        throw new Unsupported(
          '`.slice` with an end index on an arbitrary-length array is not supported',
          node,
        )

      if (!startArg || startArg.k === 'void') return list

      const refusal = () =>
        new Unsupported(
          '`.slice` on an arbitrary-length array requires a known non-negative start index (up to 8)',
          node,
        )

      const s = this.settled(startArg)
      if (!isNumber(s) || s.k !== 'scalar') throw refusal()
      const start = Number(this.settle(s.e, refusal).value)
      if (start < 0 || start > 8) throw refusal()
      let cur = list.e
      for (let i = 0; i < start; i++) cur = ir.listTail(cur)
      return { k: 'list', e: cur, ...(list.num ? { num: true } : {}) }
    }

    if (method === 'at') {
      if (args.length !== 1) throw new Unsupported('`.at` takes one argument', node)

      const refusal = () =>
        new Unsupported('`.at` on an arbitrary-length array is only supported at index 0', node)

      const s = this.settled(args[0]!)
      if (!isNumber(s) || s.k !== 'scalar') throw refusal()
      const pos = this.settle(s.e, refusal).value as bigint
      if (pos !== 0n) throw refusal()
      return this.merge(
        ir.lt(ir.lit(0n), ir.listLen(list.e)),
        scalar(ir.listHead(list.e), list.num),
        VOID,
      )
    }

    if (
      method === 'map' ||
      method === 'filter' ||
      method === 'some' ||
      method === 'every' ||
      method === 'reduce'
    ) {
      const isReduce = method === 'reduce'

      if (isReduce ? args.length !== 2 : args.length !== 1) {
        throw new Unsupported(
          isReduce
            ? '`.reduce` on an arbitrary-length array requires a callback and an initial value'
            : `\`.${method}\` takes one callback`,
          node,
        )
      }

      const cb = this.settled(args[0]!)

      if (cb.k !== 'closure')
        throw new Unsupported(`\`.${method}\` needs a function, but this is ${describe(cb)}`, node)

      const params = parametersOf(cb.node)
      const maxParams = isReduce ? 2 : 1

      if (params.length > maxParams || params.some((p) => p.dotDotDotToken)) {
        throw new Unsupported(
          `a callback of \`.${method}\` on an arbitrary-length array cannot use the index, array or rest parameters`,
          node,
        )
      }

      const elName = `_el${this.lambdaCounter++}`
      const elVal = scalar(ir.variable(elName, elemTy), list.num)
      const initIr = isReduce ? this.irArgOf(args[1]!) : undefined

      if (isReduce && !initIr)
        throw new Unsupported(
          '`.reduce` on an arbitrary-length array requires a boolean, bigint, number, string or array initial value',
          node,
        )

      const accName = isReduce ? `_acc${this.lambdaCounter++}` : undefined
      const cbArgs = isReduce
        ? [this.valueFromExpr(ir.variable(accName!, initIr!.ty), initIr!.num), elVal]
        : [elVal]
      const startObs = this.instance?.obligations.length ?? 0
      const savedPc = this.pc
      this.pc = []
      let result: Value

      try {
        result = this.unchanging(`a callback of \`.${method}\``, node, () =>
          this.call(cb, cbArgs, node),
        )
      } finally {
        this.pc = savedPc
      }

      if (result.k === 'bottom') {
        this.refuseFallOff(startObs, node)
        throw new Unsupported(
          `a callback of \`.${method}\` on an arbitrary-length array that always throws is not supported`,
          node,
        )
      }

      const THROWING = new Set<ObligationKind>([
        'unreachable',
        'nothrow',
        'undefined',
        'null',
        'tdz',
      ])
      const addedObs = this.instance ? this.instance.obligations.splice(startObs) : []

      for (const o of addedObs) {
        if (o.kind === 'expect')
          throw new Unsupported(
            `calling \`expect()\` inside \`.${method}\` on an arbitrary-length array is not supported`,
            node,
          )

        if (
          accName &&
          (ir.freeVariables(o.guard).has(accName) || ir.freeVariables(o.claim).has(accName))
        ) {
          throw new Unsupported(
            `a callback of \`.${method}\` on an arbitrary-length array that can throw or overflow depending on the accumulator is not supported`,
            node,
          )
        }

        const perElem = ir.or(ir.not(o.guard), o.claim)
        if (perElem.t === 'lit' && perElem.value === true) continue

        if (
          (method === 'some' || method === 'every') &&
          THROWING.has(o.kind) &&
          ir.freeVariables(perElem).has(elName)
        ) {
          throw new Unsupported(
            `a callback of \`.${method}\` on an arbitrary-length array that may throw depending on the element is not supported`,
            node,
          )
        }

        const allClaim = ir.listAll(list.e, elName, perElem)

        if (this.instance) {
          const guard = ir.all(this.pc)

          if (
            !(guard.t === 'lit' && guard.value === false) &&
            !(allClaim.t === 'lit' && allClaim.value === true)
          ) {
            this.instance.obligations.push({ ...o, guard, claim: allClaim })
          }
        }
      }

      if (method === 'map') {
        const res = this.settled(result)

        if (res.k !== 'scalar')
          throw new Unsupported(
            '`.map` on an arbitrary-length array must return a boolean, bigint, number or string',
            node,
          )

        return {
          k: 'list',
          e: ir.listMap(list.e, elName, res.e, ir.listTyOf(res.e.ty as ir.ScalarTy)),
          ...(res.num ? { num: true } : {}),
        }
      }

      if (method === 'filter')
        return {
          k: 'list',
          e: ir.listFilter(list.e, elName, this.truthy(result, node)),
          ...(list.num ? { num: true } : {}),
        }

      if (method === 'some') return scalar(ir.listAny(list.e, elName, this.truthy(result, node)))
      if (method === 'every') return scalar(ir.listAll(list.e, elName, this.truthy(result, node)))
      const stepIr = this.irArgOf(result, initIr!.ty, !!initIr!.num)

      if (!stepIr)
        throw new Unsupported(
          '`.reduce` on an arbitrary-length array must return the same type as its initial value',
          node,
        )

      return this.valueFromExpr(
        ir.listFold(list.e, initIr!.e, accName!, elName, stepIr.e),
        initIr!.num,
      )
    }

    throw new Unsupported(
      `the array method \`.${method}\` is not supported on an array of unknown length`,
      node,
    )
  }

  private arrayMethod(
    array: Extract<Value, { k: 'array' }>,
    method: string,
    args: Value[],
    node: N,
  ): Value {
    const items = array.items

    if (method === 'push') {
      for (const value of args) {
        this.assertChangeable(array, value, node)
        this.write(array, items.length, value)
      }

      return scalar(ir.lit(BigInt(items.length)), true)
    }

    if (method === 'pop') {
      if (args.length !== 0) throw new Unsupported('`.pop` takes no arguments', node)
      if (!items.length) return VOID
      this.assertChangeable(array, VOID, node)
      const removed = items[items.length - 1]!
      this.write(array, items.length - 1, undefined as unknown as Value)
      return removed
    }

    if (method === 'shift') {
      if (args.length !== 0) throw new Unsupported('`.shift` takes no arguments', node)
      if (!items.length) return VOID
      this.assertChangeable(array, VOID, node)
      const firstItem = items[0]!
      for (let i = 0; i < items.length - 1; i++) this.write(array, i, items[i + 1]!)
      this.write(array, items.length - 1, undefined as unknown as Value)
      return firstItem
    }

    if (method === 'unshift') {
      if (args.length > 0) {
        for (const value of args) this.assertChangeable(array, value, node)
        const old = [...items]
        const next = [...args, ...old]
        for (let i = 0; i < next.length; i++) this.write(array, i, next[i]!)
      }

      return scalar(ir.lit(BigInt(items.length)), true)
    }

    if (method === 'reverse' || method === 'toReversed') {
      if (args.length !== 0) throw new Unsupported(`\`.${method}\` takes no arguments`, node)
      const reversed = [...items].reverse()
      if (method === 'toReversed') return this.fresh({ k: 'array', items: reversed })

      for (let i = 0; i < reversed.length; i++) {
        if (items[i] === reversed[i]) continue
        this.assertChangeable(array, reversed[i]!, node)
        this.write(array, i, reversed[i]!)
      }

      return array
    }

    if (method === 'concat') {
      const concatWithList = (
        before: Value[],
        list: Extract<Value, { k: 'list' }>,
        rest: Value[],
      ): Value => {
        const prefix = this.asListExpr(
          { k: 'array', items: before },
          list.e.ty as ir.ListTy,
          !!list.num,
        )

        if (!prefix)
          throw new Unsupported(
            '`.concat` mixing an arbitrary-length array with incompatible element types is not supported',
            node,
          )

        const combined: Extract<Value, { k: 'list' }> = {
          k: 'list',
          e: ir.listConcat(prefix.e, list.e),
          ...(list.num ? { num: true } : {}),
        }
        return rest.length ? this.listMethod(combined, 'concat', rest, node) : combined
      }

      const join = (from: number, before: Value[]): Value => {
        const acc = [...before]
        let index = from

        for (; index < args.length; index++) {
          const arg = this.settled(args[index]!)
          if (arg.k === 'choice') break
          if (arg.k === 'bottom') return BOTTOM
          if (arg.k === 'list') return concatWithList(acc, arg, args.slice(index + 1))

          if (arg.k === 'array') acc.push(...arg.items)
          else acc.push(arg)
        }

        if (index === args.length) return this.fresh({ k: 'array', items: acc })
        return this.over(args[index]!, (arg) => {
          if (arg.k === 'bottom') return BOTTOM
          if (arg.k === 'list') return concatWithList(acc, arg, args.slice(index + 1))
          return join(index + 1, arg.k === 'array' ? [...acc, ...arg.items] : [...acc, arg])
        })
      }

      return join(0, items)
    }

    if (method === 'join') {
      if (args.length > 1) throw new Unsupported('`.join` takes at most one separator', node)
      const sepVal =
        args.length === 0
          ? scalar(ir.lit(','))
          : this.over(args[0]!, (s) => {
              if (s.k === 'bottom') return BOTTOM
              if (s.k === 'void') return scalar(ir.lit(','))
              return this.text(s, node, true)
            })
      if (sepVal.k === 'bottom') return BOTTOM
      const sep = this.scalarOf(sepVal, node, 'str')
      let out: Expr = ir.lit('')

      for (let i = 0; i < items.length; i++) {
        if (i > 0) out = ir.concat(out, sep)
        const part = this.over(items[i]!, (item) => {
          if (item.k === 'bottom') return BOTTOM
          if (item.k === 'void' || item.k === 'null') return scalar(ir.lit(''))
          return this.text(item, node, true)
        })
        if (part.k === 'bottom') return BOTTOM
        out = ir.concat(out, this.scalarOf(part, node, 'str'))
      }

      return scalar(out)
    }

    if (method === 'flat') {
      if (args.length > 1) throw new Unsupported('`.flat` takes at most one depth', node)
      let depth = 1

      if (args[0] && args[0].k !== 'void') {
        const arg0 = this.settled(args[0])
        if (arg0.k === 'bottom') return BOTTOM
        const refusal = () => new Unsupported('`.flat` requires a depth known here', node)

        if (arg0.k === 'infinite') depth = arg0.negative ? 0 : Infinity
        else if (!isNumber(arg0) || arg0.k !== 'scalar') throw refusal()
        else depth = Math.max(0, Number(this.settle(arg0.e, refusal).value))
      }

      const mayBeArray = (v: Value): boolean =>
        v.k === 'array' ||
        v.k === 'list' ||
        (v.k === 'choice' && (mayBeArray(v.a) || mayBeArray(v.b)))

      const flatten = (list: Value[], d: number): Value[] => {
        const out: Value[] = []

        for (const item of list) {
          const settled = this.settled(item)

          if (d > 0 && settled.k === 'array') out.push(...flatten(settled.items, d - 1))
          else if (d > 0 && settled.k === 'list')
            throw new Unsupported(
              '`.flat` over an arbitrary-length array element is not supported',
              node,
            )
          else if (d > 0 && settled.k === 'choice' && mayBeArray(settled))
            throw new Unsupported(
              '`.flat` over an element that may or may not be an array is not supported',
              node,
            )
          else out.push(settled)
        }

        return out
      }

      return this.fresh({ k: 'array', items: flatten(items, depth) })
    }

    const invoke = (fn: Value, values: Value[]): Value => {
      if (fn.k === 'choice')
        return this.branch(
          fn.cond,
          () => invoke(fn.a, values),
          () => invoke(fn.b, values),
        )

      if (fn.k === 'closure') {
        const params = parametersOf(fn.node)

        if (params.length > values.length || params.some((p) => p.dotDotDotToken)) {
          throw new Unsupported(
            'an array callback that takes the array itself or rest parameters is not supported',
            node,
          )
        }
      }

      return this.call(fn, values, node)
    }

    const callable = (fn: Value | undefined): boolean =>
      fn?.k === 'closure' || (fn?.k === 'choice' && callable(fn.a) && callable(fn.b))

    const position = (index: number) => scalar(ir.lit(BigInt(index)), true)

    const known = (value: Value | undefined, fallback: number, what: string) => {
      if (!value || value.k === 'void') return fallback

      const refusal = () =>
        new Unsupported(`\`.${method}\` is supported with ${what} known here`, node)

      if (!isNumber(value) || value.k !== 'scalar') throw refusal()
      const given = Number(this.settle(value.e, refusal).value)
      return given < 0 ? items.length + given : given
    }

    const [first, second] = args

    if (method === 'sort' || method === 'toSorted') {
      if (args.length !== 1 || !callable(first))
        throw new Unsupported(
          `\`.${method}\` is supported with a comparing function; without one it compares the elements as text`,
          node,
        )

      const order = this.sorted(items, (a, b) => invoke(first!, [a, b]), node)
      if (method === 'toSorted') return this.fresh({ k: 'array', items: order })
      order.forEach((item, index) => {
        if (items[index] === item) return
        this.assertChangeable(array, item, node)
        this.write(array, index, item)
      })
      return array
    }

    if (ARRAY_MUTATORS.has(method))
      throw new Unsupported(
        `\`.${method}\` changes the array in place in a way that is not modeled; only \`.push\`, \`.pop\`, \`.shift\`, \`.unshift\`, \`.reverse\`, \`.sort\` and assigning to a position are`,
        node,
      )

    if (method === 'at') {
      if (args.length > 1) throw new Unsupported('`.at` takes one position', node)
      if (!first || first.k === 'void') return items[0] ?? this.absent(undefined, node)
      return this.over(first, (idx) => {
        if (idx.k === 'bottom') return BOTTOM
        if (idx.k === 'void') return items[0] ?? this.absent(undefined, node)
        const refusal = () => new Unsupported('`.at` is supported with a position known here', node)
        if (!isNumber(idx) || idx.k !== 'scalar') throw refusal()
        return this.indexArray(items, idx.e, node, true, refusal)
      })
    }

    if (method === 'slice') {
      if (args.length > 2) throw new Unsupported('`.slice` takes a start and an end', node)
      const clamp = (index: number) => Math.min(Math.max(index, 0), items.length)
      return this.fresh({
        k: 'array',
        items: items.slice(
          clamp(known(first, 0, 'a start')),
          clamp(known(second, items.length, 'an end')),
        ),
      })
    }

    if (method === 'with') {
      if (args.length > 2) throw new Unsupported('`.with` takes a position and a value', node)
      if (second?.k === 'bottom') return BOTTOM
      return this.over(first ?? VOID, (idx) => {
        if (idx.k === 'bottom') return BOTTOM
        const pos = known(idx, 0, 'a position')

        if (pos < 0 || pos >= items.length) {
          this.emit('unreachable', ir.FALSE, node)
          return BOTTOM
        }

        const copy = [...items]
        copy[pos] = second ?? VOID
        return this.fresh({ k: 'array', items: copy })
      })
    }

    if (method === 'toSpliced') {
      if (args.some((a) => a.k === 'bottom')) return BOTTOM
      if (args.length === 0) return this.fresh({ k: 'array', items: [...items] })
      const clamp = (index: number) => Math.min(Math.max(index, 0), items.length)
      const start = clamp(known(first, 0, 'a start'))
      let deleteCount = items.length - start

      if (args.length >= 2) {
        if (!second || second.k === 'void') deleteCount = 0
        else if (!isNumber(second) || second.k !== 'scalar')
          throw new Unsupported('`.toSpliced` is supported with a delete count known here', node)
        else
          deleteCount = Math.max(
            0,
            Number(
              this.settle(
                second.e,
                () =>
                  new Unsupported('`.toSpliced` is supported with a delete count known here', node),
              ).value,
            ),
          )
      }

      const copy = [...items]
      copy.splice(start, deleteCount, ...args.slice(2))
      return this.fresh({ k: 'array', items: copy })
    }

    if (method === 'indexOf' || method === 'lastIndexOf') {
      if (args.length < 1 || args.length > 2)
        throw new Unsupported(
          `\`.${method}\` takes a search value and an optional start index`,
          node,
        )

      if (first!.k === 'bottom') return BOTTOM
      const hasFrom = args.length === 2

      const search = (fromArg: Value): Value => {
        if (fromArg.k === 'bottom') return BOTTOM
        const defaultFrom = method === 'indexOf' ? 0 : hasFrom ? 0 : items.length - 1
        const from =
          method === 'indexOf'
            ? Math.max(0, known(fromArg, defaultFrom, 'a start position'))
            : Math.min(items.length - 1, known(fromArg, defaultFrom, 'a start position'))
        let result: Expr = ir.lit(-1n)
        const forward = method === 'indexOf'

        for (
          let index = forward ? items.length - 1 : 0;
          forward ? index >= from : index <= from;
          index += forward ? -1 : 1
        ) {
          const eq = this.eqValues(items[index]!, first!, node)
          if (eq.k === 'bottom') return BOTTOM
          result = ir.ite(this.scalarOf(eq, node, 'bool'), ir.lit(BigInt(index)), result)
        }

        return scalar(result, true)
      }

      return hasFrom ? this.over(second!, search) : search(VOID)
    }

    if (
      ![
        'includes',
        'some',
        'every',
        'map',
        'reduce',
        'reduceRight',
        'filter',
        'find',
        'findIndex',
        'findLast',
        'findLastIndex',
        'flatMap',
        'forEach',
      ].includes(method)
    ) {
      throw new Unsupported(`the array method \`.${method}\` is not supported`, node)
    }

    const isReduce = method === 'reduce' || method === 'reduceRight'

    if (!first || (isReduce ? args.length > 2 : args.length !== 1)) {
      throw new Unsupported(
        isReduce
          ? `\`.${method}\` is supported with a callback and an optional initial value`
          : `\`.${method}\` is supported with exactly one argument`,
        node,
      )
    }

    if (method !== 'includes' && !callable(first))
      throw new Unsupported(`\`.${method}\` needs a function, but this is ${describe(first)}`, node)

    switch (method) {
      case 'reduce':
      case 'reduceRight': {
        const hasInit = args.length === 2

        if (!hasInit && items.length === 0) {
          this.emit('unreachable', ir.FALSE, node)
          return BOTTOM
        }

        const right = method === 'reduceRight'
        const length = items.length
        let accumulator = hasInit ? second! : items[right ? length - 1 : 0]!

        for (
          let index = right ? (hasInit ? length - 1 : length - 2) : hasInit ? 0 : 1;
          right ? index >= 0 : index < length;
          index += right ? -1 : 1
        ) {
          if (index >= items.length) continue
          const started = this.instance?.obligations.length ?? 0
          accumulator = invoke(first, [accumulator, items[index]!, position(index)])

          if (accumulator.k === 'bottom') {
            this.refuseFallOff(started, node)
            return BOTTOM
          }
        }

        return accumulator
      }
      case 'forEach': {
        const length = items.length

        for (let index = 0; index < length; index++) {
          if (index >= items.length) continue
          const started = this.instance?.obligations.length ?? 0
          const answer = invoke(first, [items[index]!, position(index)])

          if (answer.k === 'bottom') {
            this.refuseFallOff(started, node)
            return BOTTOM
          }
        }

        return VOID
      }
      case 'includes':
        return this.arrayContains(items, first, node)
      case 'some':
      case 'every':
      case 'find':
      case 'findIndex':
      case 'findLast':
      case 'findLastIndex': {
        const reverse = method === 'findLast' || method === 'findLastIndex'
        const settles = method === 'every' ? ir.not : (pass: Expr) => pass
        const order = items.map((item, index) => ({ item, index }))
        if (reverse) order.reverse()
        const asked = this.unchanging(`a callback of \`.${method}\``, node, () => {
          let reached: Expr = ir.TRUE
          return order.map(({ item, index }) => {
            if (reached.t === 'lit' && !reached.value)
              return { item, index, pass: method === 'every' ? ir.TRUE : ir.FALSE }

            const started = this.instance?.obligations.length ?? 0
            const answer = this.under(reached, () => invoke(first, [item, position(index)]))
            if (answer.k === 'bottom') this.refuseFallOff(started, node)
            const pass =
              answer.k === 'bottom'
                ? method === 'every'
                  ? ir.TRUE
                  : ir.FALSE
                : this.truthy(answer, node)
            reached = answer.k === 'bottom' ? ir.FALSE : ir.and(reached, ir.not(settles(pass)))
            return { item, index, pass }
          })
        })
        if (method === 'some') return scalar(asked.map(({ pass }) => pass).reduce(ir.or, ir.FALSE))
        if (method === 'every') return scalar(asked.map(({ pass }) => pass).reduce(ir.and, ir.TRUE))

        if (method === 'findIndex' || method === 'findLastIndex') {
          return scalar(
            asked.reduceRight<Expr>(
              (later, { index, pass }) => ir.ite(pass, ir.lit(BigInt(index)), later),
              ir.lit(-1n),
            ),
            true,
          )
        }

        return asked.reduceRight<Value>(
          (later, { item, pass }) =>
            this.branch(
              pass,
              () => item,
              () => later,
            ),
          VOID,
        )
      }
      case 'map': {
        const mapped: Value[] = []
        const length = items.length

        for (let index = 0; index < length; index++) {
          if (index >= items.length)
            throw new Unsupported(
              'a callback that shrinks the array being mapped is not supported',
              node,
            )

          const started = this.instance?.obligations.length ?? 0
          const answer = invoke(first, [items[index]!, position(index)])

          if (answer.k === 'bottom') {
            this.refuseFallOff(started, node)
            return BOTTOM
          }

          mapped.push(answer)
        }

        return this.fresh({ k: 'array', items: mapped })
      }
      case 'filter': {
        const asked: { item: Value; pass: Expr }[] = []
        const length = items.length

        for (let index = 0; index < length; index++) {
          if (index >= items.length) continue
          const item = items[index]!
          const started = this.instance?.obligations.length ?? 0
          const answer = invoke(first, [item, position(index)])

          if (answer.k === 'bottom') {
            this.refuseFallOff(started, node)
            return BOTTOM
          }

          asked.push({ item, pass: this.truthy(answer, node) })
        }

        if (asked.filter(({ pass }) => pass.t !== 'lit').length > MAX_UNDECIDED)
          throw new Unsupported(
            `\`.filter\` over more than ${MAX_UNDECIDED} elements that may or may not pass is not supported`,
            node,
          )

        const keep = (from: number, before: Value[]): Value => {
          const kept = [...before]
          let index = from

          for (; index < asked.length && asked[index]!.pass.t === 'lit'; index++)
            if ((asked[index]!.pass as { value: Scalar }).value) kept.push(asked[index]!.item)

          if (index === asked.length) return this.fresh({ k: 'array', items: kept })
          return this.branch(
            asked[index]!.pass,
            () => keep(index + 1, [...kept, asked[index]!.item]),
            () => keep(index + 1, kept),
          )
        }

        return keep(0, [])
      }
      case 'flatMap': {
        const parts: Value[] = []
        const length = items.length

        for (let index = 0; index < length; index++) {
          if (index >= items.length) continue
          const started = this.instance?.obligations.length ?? 0
          const answer = invoke(first, [items[index]!, position(index)])

          if (answer.k === 'bottom') {
            this.refuseFallOff(started, node)
            return BOTTOM
          }

          parts.push(
            this.over(answer, (part) =>
              part.k === 'array' ? this.fresh({ k: 'array', items: [...part.items] }) : part,
            ),
          )
        }

        let undecided = 0

        const count = (part: Value): void => {
          if (part.k === 'choice') {
            undecided++
            count(part.a)
            count(part.b)
          }
        }

        parts.forEach(count)

        if (undecided > MAX_UNDECIDED)
          throw new Unsupported(
            `\`.flatMap\` over more than ${MAX_UNDECIDED} results that depend on a condition is not supported`,
            node,
          )

        const join = (from: number, before: Value[]): Value => {
          const joined = [...before]
          let index = from

          for (; index < parts.length; index++) {
            const part = this.settled(parts[index]!)
            if (part.k === 'choice') break
            if (part.k === 'bottom') return BOTTOM

            if (part.k === 'list')
              throw new Unsupported(
                '`.flatMap` returning an arbitrary-length array is not supported',
                node,
              )

            if (part.k === 'array') joined.push(...part.items)
            else joined.push(part)
          }

          if (index === parts.length) return this.fresh({ k: 'array', items: joined })
          return this.over(parts[index]!, (part) => {
            if (part.k === 'bottom') return BOTTOM

            if (part.k === 'list')
              throw new Unsupported(
                '`.flatMap` returning an arbitrary-length array is not supported',
                node,
              )

            return join(
              index + 1,
              part.k === 'array' ? [...joined, ...part.items] : [...joined, part],
            )
          })
        }

        return join(0, [])
      }
      default:
        throw new Unsupported(`the array method \`.${method}\` is not supported`, node)
    }
  }

  private refuseFallOff(since: number, node: N) {
    if (
      this.instance?.obligations.slice(since).some((obligation) => obligation.kind === 'falloff')
    ) {
      throw new Unsupported(
        'a callback that ends without returning a value is not supported here; return a value on every path',
        node,
      )
    }
  }

  private sorted(items: Value[], compare: (a: Value, b: Value) => Value, node: N): Value[] {
    if (items.some((item) => item.k === 'void' || item.k === 'choice' || item.k === 'bottom'))
      throw new Unsupported('sorting a list that may hold undefined is not supported', node)

    if (items.length > MAX_SORTED)
      throw new Unsupported(`sorting more than ${MAX_SORTED} elements is not supported`, node)

    const refusal = () =>
      new Unsupported(
        'sorting is supported where the order of the elements is known here: each comparison has to come out as a known number',
        node,
      )

    const started = this.instance?.obligations.length ?? 0
    const signs = this.unchanging('a comparing function of `.sort`', node, () =>
      items.map((a) =>
        items.map((b) => {
          const result = compare(a, b)
          if (!isNumber(result) || result.k !== 'scalar') throw refusal()
          const value = this.settle(result.e, refusal).value as bigint
          return value < 0n ? -1 : value > 0n ? 1 : 0
        }),
      ),
    )

    if ((this.instance?.obligations.length ?? 0) > started)
      throw new Unsupported(
        'a comparing function of `.sort` that asserts, or that could throw, is not supported',
        node,
      )

    const n = items.length

    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (signs[i]![j]! !== -signs[j]![i]!)
          throw new Unsupported(
            'this comparing function does not order the elements consistently, so the result of sorting is not defined',
            node,
          )

        for (let k = 0; k < n; k++) {
          if (signs[i]![j]! <= 0 && signs[j]![k]! <= 0 && signs[i]![k]! > 0)
            throw new Unsupported(
              'this comparing function does not order the elements consistently, so the result of sorting is not defined',
              node,
            )
        }
      }
    }

    return items
      .map((_, index) => index)
      .sort((i, j) => signs[i]![j]! || i - j)
      .map((index) => items[index]!)
  }

  private arrayFrom(args: Value[], node: N): Value {
    this.assertBuiltinsIntact(node)
    const [source, given] = args
    const make = given?.k === 'void' ? undefined : given

    if (!source || args.length > 2)
      throw new Unsupported('`Array.from` is supported with a list and an optional function', node)

    if (make && make.k !== 'closure')
      throw new Unsupported(`\`Array.from\` needs a function, but this is ${describe(make)}`, node)

    if (make && parametersOf(make.node).length > 2)
      throw new Unsupported(
        'a function given to `Array.from` takes an element and its position',
        node,
      )

    return this.over(source, (from) => {
      if (from.k === 'bottom') return BOTTOM
      let items: Value[]

      if (from.k === 'record') {
        const length = from.fields.get('length')

        const refusal = () =>
          new Unsupported(
            '`Array.from` of an object is supported for `{ length }` with a length known here',
            node,
          )

        if (from.fields.size !== 1 || !length || !isNumber(length) || length.k !== 'scalar')
          throw refusal()

        const count = Number(this.settle(length.e, refusal).value)

        if (count > MAX_ITERATIONS)
          throw new Unsupported(
            `a list of more than ${MAX_ITERATIONS} elements is too long to build`,
            node,
          )

        items = Array.from({ length: Math.max(count, 0) }, () => VOID)
      } else {
        const listed = this.listed(from, node)

        if (listed.k !== 'array')
          throw new Unsupported(`\`Array.from\` of ${describe(from)} is not supported`, node)

        items = listed.items
      }

      if (!make) return this.fresh({ k: 'array', items: [...items] })
      const activeIter = from.k === 'iterator' ? from.state : undefined
      const collection =
        from.k === 'iterator'
          ? from.source
          : from.k === 'map' || from.k === 'set'
            ? from
            : undefined
      const entered = collection ? collection.log.items.length : undefined
      const made: Value[] = []
      if (activeIter) this.activeIterators.add(activeIter)

      try {
        for (let index = 0; index < items.length; index++) {
          if (index >= MAX_ITERATIONS)
            throw new Unsupported(
              `a list of more than ${MAX_ITERATIONS} elements is too long to build`,
              node,
            )

          const started = this.instance?.obligations.length ?? 0
          const item = this.call(make, [items[index]!, scalar(ir.lit(BigInt(index)), true)], node)

          if (item.k === 'bottom') {
            this.refuseFallOff(started, node)
            return BOTTOM
          }

          made.push(item)

          if (entered !== undefined && collection!.log.items.length !== entered) {
            throw new Unsupported(
              'changing a Map or a Set inside the function that `Array.from` walks it with is not supported',
              node,
            )
          }
        }
      } finally {
        if (activeIter) this.activeIterators.delete(activeIter)
      }

      return this.fresh({ k: 'array', items: made })
    })
  }

  private construct(node: N, env: Env): Value {
    const callee = node.expression
    const kind =
      callee.kind === K.Identifier && !env.get(callee.text) && this.isBuiltin(callee)
        ? callee.text === 'Map'
          ? 'map'
          : callee.text === 'Set'
            ? 'set'
            : undefined
        : undefined

    if (!kind)
      throw new Unsupported(
        '`new` is supported for Map and Set only; classes are not modeled',
        node,
      )

    this.assertBuiltinsIntact(node)
    const args = this.arguments({ arguments: node.arguments ?? [] }, env)
    if (args.length > 1) throw new Unsupported(`\`new ${callee.text}\` takes one list`, node)
    return this.over(args[0] ?? VOID, (given) => {
      if (given.k === 'bottom') return BOTTOM
      const collection: Extract<Value, { k: 'map' | 'set' }> = {
        k: kind,
        log: this.fresh({ k: 'array', items: [] }),
      }
      if (given.k === 'void' || given.k === 'null') return collection
      const source = this.listed(given, node)

      if (source.k !== 'array')
        throw new Unsupported(`\`new ${callee.text}\` of ${describe(given)} is not supported`, node)

      for (const item of source.items) {
        if (kind === 'set') this.add(collection, [item], node)
        else {
          const pair = this.settled(item)

          if (pair.k !== 'array' || pair.items.length < 2)
            throw new Unsupported('`new Map` needs a list of `[key, value]` pairs', node)

          this.add(collection, [pair.items[0]!, pair.items[1]!], node)
        }
      }

      return collection
    })
  }

  private add(collection: Extract<Value, { k: 'map' | 'set' }>, entry: Value[], node: N) {
    const stored = this.fresh({
      k: 'array' as const,
      items: [this.key(entry[0]!, node), ...entry.slice(1)],
    })
    this.assertChangeable(collection.log, stored, node)
    this.write(collection.log, collection.log.items.length, stored)
    this.freeze(stored)
  }

  private key(value: Value, node: N): Extract<Value, { k: 'scalar' }> {
    value = this.settled(value)

    if (value.k !== 'scalar')
      throw new Unsupported(
        `a Map or a Set is modeled with booleans, numbers, bigints and strings as keys, but this is ${describe(value)}`,
        node,
      )

    return value
  }

  private sameKey(a: Extract<Value, { k: 'scalar' }>, b: Extract<Value, { k: 'scalar' }>): Expr {
    return a.e.ty === b.e.ty && !!a.num === !!b.num ? ir.eq(a.e, b.e) : ir.FALSE
  }

  private entries(
    collection: Extract<Value, { k: 'map' | 'set' }>,
  ): { key?: Extract<Value, { k: 'scalar' }>; value: Value; kind: 'set' | 'delete' | 'clear' }[] {
    type Entry = {
      key?: Extract<Value, { k: 'scalar' }>
      value: Value
      kind: 'set' | 'delete' | 'clear'
    }

    const entryOf = (entry: Value): Entry => {
      if (entry.k === 'choice') {
        const a = entryOf(entry.a)
        const b = entryOf(entry.b)

        if (
          (a.kind === 'set' || a.kind === 'delete') &&
          a.kind === b.kind &&
          a.key &&
          b.key &&
          a.key.e.ty === b.key.e.ty &&
          !!a.key.num === !!b.key.num
        ) {
          const key = scalar(ir.ite(entry.cond, a.key.e, b.key.e), a.key.num) as Extract<
            Value,
            { k: 'scalar' }
          >
          return a.kind === 'delete'
            ? { kind: 'delete', key, value: VOID }
            : { kind: 'set', key, value: this.mergeHeld(entry.cond, a.value, b.value) }
        }

        throw new Unsupported(
          'a Map or a Set updated incompatibly on the two sides of a condition is not supported',
          undefined,
        )
      }

      if (entry.k !== 'array') throw new Error('an entry of a Map or a Set is a list')
      const [first, second] = entry.items
      if (first?.k === 'tombstone') return { kind: 'clear', value: VOID }

      if (second?.k === 'tombstone')
        return { kind: 'delete', key: first as Extract<Value, { k: 'scalar' }>, value: VOID }

      return { kind: 'set', key: first as Extract<Value, { k: 'scalar' }>, value: second ?? first! }
    }

    let start = 0

    for (let i = collection.log.items.length - 1; i >= 0; i--) {
      const item = collection.log.items[i]!

      if (item.k === 'array' && item.items[0]?.k === 'tombstone') {
        start = i + 1
        break
      }
    }

    return collection.log.items.slice(start).map(entryOf)
  }

  private copied(value: Value, at: N, verb: string, where: string): Value {
    return this.over(value, (given) => {
      if (given.k === 'bottom') return BOTTOM
      const list = this.listed(given, at)
      if (list.k !== 'array') throw new Unsupported(`${verb} ${describe(list)} ${where}`, at)
      return this.fresh({ k: 'array', items: [...list.items] })
    })
  }

  private presentBefore(
    entries: ReturnType<Translator['entries']>,
    key: Extract<Value, { k: 'scalar' }>,
    end: number,
  ): Expr {
    let present: Expr = ir.FALSE

    for (let i = 0; i < end; i++) {
      const entry = entries[i]!

      if (entry.kind === 'clear') present = ir.FALSE
      else if (entry.kind === 'delete')
        present = ir.and(present, ir.not(this.sameKey(entry.key!, key)))
      else present = ir.or(present, this.sameKey(entry.key!, key))
    }

    return present
  }

  private collectionSize(collection: Extract<Value, { k: 'map' | 'set' }>, node: N): Value {
    this.assertBuiltinsIntact(node)
    const entries = this.entries(collection)
    let size: Expr = ir.lit(0n)

    for (let i = 0; i < entries.length; i++) {
      const entry = entries[i]!
      if (entry.kind !== 'set') continue
      let superseded: Expr = ir.FALSE

      for (let j = i + 1; j < entries.length; j++) {
        const later = entries[j]!

        if (later.kind === 'clear') {
          superseded = ir.TRUE
          break
        }

        superseded = ir.or(superseded, this.sameKey(later.key!, entry.key!))
      }

      size = ir.add(size, ir.ite(superseded, ir.lit(0n), ir.lit(1n)))
    }

    return scalar(size, true)
  }

  private collectionMethod(
    collection: Extract<Value, { k: 'map' | 'set' }>,
    method: string,
    args: Value[],
    node: N,
  ): Value {
    const [first, second] = args

    const lookupKey = (v: Value): Extract<Value, { k: 'scalar' }> | undefined => {
      if (v.k === 'scalar') return v

      if (v.k === 'float')
        return Number.isSafeInteger(v.value)
          ? (scalar(ir.lit(BigInt(v.value)), true) as Extract<Value, { k: 'scalar' }>)
          : undefined

      if (v.k === 'rat' || v.k === 'quot')
        throw new Unsupported(
          'looking up a fractional number in a Map or Set is not supported',
          node,
        )

      return undefined
    }

    if (collection.k === 'map' && method === 'set' && args.length === 2) {
      this.add(collection, [first!, second!], node)
      return collection
    }

    if (collection.k === 'set' && method === 'add' && args.length === 1) {
      this.add(collection, [first!], node)
      return collection
    }

    if (method === 'clear' && args.length === 0) {
      const marker = this.fresh({ k: 'array' as const, items: [TOMBSTONE] })
      this.assertChangeable(collection.log, marker, node)
      this.write(collection.log, collection.log.items.length, marker)
      this.freeze(marker)
      return VOID
    }

    if (method === 'delete' && args.length === 1) {
      return this.over(first!, (wanted) => {
        if (wanted.k === 'bottom') return BOTTOM
        const key = lookupKey(wanted)
        if (!key) return scalar(ir.FALSE)
        const entries = this.entries(collection)
        const existed = this.presentBefore(entries, key, entries.length)
        const marker = this.fresh({ k: 'array' as const, items: [key, TOMBSTONE] })
        this.assertChangeable(collection.log, marker, node)
        this.write(collection.log, collection.log.items.length, marker)
        this.freeze(marker)
        return scalar(existed)
      })
    }

    if (method === 'forEach' && args.length === 1) {
      const callable = (fn: Value | undefined): boolean =>
        fn?.k === 'closure' || (fn?.k === 'choice' && callable(fn.a) && callable(fn.b))

      if (!callable(first))
        throw new Unsupported(
          `\`.forEach\` needs a function, but this is ${describe(first!)}`,
          node,
        )

      const checkParams = (fn: Value): void => {
        if (fn.k === 'choice') {
          checkParams(fn.a)
          checkParams(fn.b)
          return
        }

        if (fn.k === 'closure') {
          const params = parametersOf(fn.node)

          if (params.length > 2 || params.some((p) => p.dotDotDotToken)) {
            throw new Unsupported(
              'a `.forEach` callback that takes the collection itself or rest parameters is not supported',
              node,
            )
          }
        }
      }

      checkParams(first!)
      const listed = this.listed(collection, node)
      if (listed.k !== 'array') throw new Error('listed collection is an array')
      const entered = collection.log.items.length

      for (const item of listed.items) {
        const cbArgs =
          collection.k === 'map'
            ? [
                (item as Extract<Value, { k: 'array' }>).items[1]!,
                (item as Extract<Value, { k: 'array' }>).items[0]!,
              ]
            : [item, item]
        const started = this.instance?.obligations.length ?? 0
        const answer = this.call(first!, cbArgs, node)

        if (answer.k === 'bottom') {
          this.refuseFallOff(started, node)
          return BOTTOM
        }

        if (collection.log.items.length !== entered) {
          throw new Unsupported('changing a Map or a Set inside `.forEach` is not supported', node)
        }
      }

      return VOID
    }

    if ((method === 'keys' || method === 'values' || method === 'entries') && args.length === 0) {
      return {
        k: 'iterator',
        source: collection,
        mode: method,
        state: this.fresh({ k: 'record', fields: new Map([['done', scalar(ir.FALSE)]]) }),
      }
    }

    if ((method === 'has' || (method === 'get' && collection.k === 'map')) && args.length === 1) {
      const entries = this.entries(collection)
      return this.over(first!, (wanted) => {
        if (wanted.k === 'bottom') return BOTTOM
        const key = lookupKey(wanted)

        if (method === 'has')
          return scalar(key ? this.presentBefore(entries, key, entries.length) : ir.FALSE)

        if (!key) return VOID
        let result: Value = VOID

        for (const entry of entries) {
          if (entry.kind === 'clear') result = VOID
          else if (entry.kind === 'delete')
            result = this.branch(
              this.sameKey(entry.key!, key),
              () => VOID,
              () => result,
            )
          else
            result = this.branch(
              this.sameKey(entry.key!, key),
              () => entry.value,
              () => result,
            )
        }

        return result
      })
    }

    if (
      collection.k === 'set' &&
      args.length === 1 &&
      [
        'union',
        'intersection',
        'difference',
        'symmetricDifference',
        'isSubsetOf',
        'isSupersetOf',
        'isDisjointFrom',
      ].includes(method)
    ) {
      return this.over(first!, (other) => {
        if (other.k === 'bottom') return BOTTOM

        if (other.k !== 'set')
          throw new Unsupported(
            `\`.${method}\` is supported with another Set, but found ${describe(other)}`,
            node,
          )

        if (method === 'isSubsetOf' || method === 'isSupersetOf' || method === 'isDisjointFrom') {
          const left = this.entries(method === 'isSupersetOf' ? other : collection)
          const right = this.entries(method === 'isSupersetOf' ? collection : other)
          let holds: Expr = ir.TRUE

          for (let i = 0; i < left.length; i++) {
            const entry = left[i]!
            if (entry.kind !== 'set') continue
            let superseded: Expr = ir.FALSE

            for (let j = i + 1; j < left.length; j++) {
              const later = left[j]!

              if (later.kind === 'clear') {
                superseded = ir.TRUE
                break
              }

              superseded = ir.or(superseded, this.sameKey(later.key!, entry.key!))
            }

            const inRight = this.presentBefore(right, entry.key!, right.length)
            const cond = method === 'isDisjointFrom' ? ir.not(inRight) : inRight
            holds = ir.and(holds, ir.or(superseded, cond))
          }

          return scalar(holds)
        }

        const aList = (this.listed(collection, node) as Extract<Value, { k: 'array' }>)
          .items as Extract<Value, { k: 'scalar' }>[]
        const bList = (this.listed(other, node) as Extract<Value, { k: 'array' }>).items as Extract<
          Value,
          { k: 'scalar' }
        >[]

        const refusal = () =>
          new Unsupported(
            `\`.${method}\` is supported where it is known here which keys are equal`,
            node,
          )

        const hasKey = (
          list: Extract<Value, { k: 'scalar' }>[],
          key: Extract<Value, { k: 'scalar' }>,
        ) => list.some((item) => this.settle(this.sameKey(item, key), refusal).value === true)

        const result: Extract<Value, { k: 'set' }> = {
          k: 'set',
          log: this.fresh({ k: 'array', items: [] }),
        }

        if (method === 'union') {
          for (const k of aList) this.add(result, [k], node)
          for (const k of bList) if (!hasKey(aList, k)) this.add(result, [k], node)
        } else if (method === 'intersection') {
          const [small, large] = aList.length <= bList.length ? [aList, bList] : [bList, aList]
          for (const k of small) if (hasKey(large, k)) this.add(result, [k], node)
        } else if (method === 'difference') {
          for (const k of aList) if (!hasKey(bList, k)) this.add(result, [k], node)
        } else {
          for (const k of aList) if (!hasKey(bList, k)) this.add(result, [k], node)
          for (const k of bList) if (!hasKey(aList, k)) this.add(result, [k], node)
        }

        return result
      })
    }

    throw new Unsupported(
      `calling \`.${method}\` on ${describe(collection)} is not supported`,
      node,
    )
  }

  private listed(value: Value, node: N): Value {
    value = this.settled(value)

    if (value.k === 'iterator') {
      this.assertBuiltinsIntact(node)

      if (this.activeIterators.has(value.state)) {
        throw new Unsupported(
          'consuming a Map or Set iterator while it is already being iterated is not supported',
          node,
        )
      }

      const doneVal = this.settled(value.state.fields.get('done')!)
      const done = this.settle(
        this.scalarOf(doneVal, node, 'bool'),
        () =>
          new Unsupported(
            'consuming a Map or Set iterator that may already have been exhausted on another branch is not supported',
            node,
          ),
      ).value as boolean
      if (done) return this.fresh({ k: 'array', items: [] })
      this.assertChangeable(value.state, scalar(ir.TRUE), node)
      this.write(value.state, 'done', scalar(ir.TRUE))
      const list = this.listed(value.source, node)
      if (list.k !== 'array') throw new Error('listed collection is an array')

      if (value.source.k === 'set') {
        if (value.mode === 'entries')
          return this.fresh({
            k: 'array',
            items: list.items.map((item) => this.fresh({ k: 'array', items: [item, item] })),
          })

        return list
      }

      if (value.mode === 'entries') return list
      return this.fresh({
        k: 'array',
        items: list.items.map(
          (pair) => (pair as Extract<Value, { k: 'array' }>).items[value.mode === 'keys' ? 0 : 1]!,
        ),
      })
    }

    if (value.k !== 'map' && value.k !== 'set') return value
    this.assertBuiltinsIntact(node)

    const refusal = () =>
      new Unsupported(
        `going through ${describe(value)} is supported where it is known here which of its keys are equal`,
        node,
      )

    const kept: { key: Extract<Value, { k: 'scalar' }>; value: Value }[] = []

    for (const entry of this.entries(value)) {
      if (entry.kind === 'clear') {
        kept.length = 0
        continue
      }

      const matchIndex = kept.findIndex(
        (seen) => this.settle(this.sameKey(seen.key, entry.key!), refusal).value === true,
      )

      if (entry.kind === 'delete') {
        if (matchIndex >= 0) kept.splice(matchIndex, 1)
        continue
      }

      if (matchIndex >= 0) kept[matchIndex]!.value = entry.value
      else kept.push({ key: entry.key!, value: entry.value })
    }

    return this.fresh({
      k: 'array',
      items: kept.map((entry) =>
        value.k === 'set' ? entry.key : this.fresh({ k: 'array', items: [entry.key, entry.value] }),
      ),
    })
  }

  private isNamespace(node: N, env: Env): boolean {
    if (node.kind !== K.Identifier || env.get(node.text)) return false
    let symbol = this.checker.getSymbolAtLocation(node)
    if (symbol && symbol.flags & SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol)
    return (
      !!symbol && (symbol.flags & (SymbolFlags.ValueModule | SymbolFlags.NamespaceModule)) !== 0
    )
  }

  private global(node: N, shorthand = false): Value {
    let symbol = shorthand
      ? this.checker.getShorthandAssignmentValueSymbol(node.parent)
      : this.checker.getSymbolAtLocation(node)
    if (symbol && symbol.flags & SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol)
    const declaration = symbol?.valueDeclaration?.resolve() as N

    if (!symbol || !declaration)
      throw new Unsupported(`\`${node.text}\` is not a value that can be translated`, node)

    const file = declaration.getSourceFile() as SourceFile

    if (file.isDeclarationFile || this.program.isSourceFileFromExternalLibrary(file)) {
      throw new Unsupported(
        `\`${node.text}\` comes from a declaration file or a library, so its code cannot be read`,
        node,
      )
    }

    this.reached.add(file.fileName)
    this.activeReached?.add(file.fileName)

    if (declaration.kind === K.FunctionDeclaration) {
      if (declaration.parent.kind !== K.SourceFile)
        throw new Unsupported(
          `\`${node.text}\` is a local function that is not in scope here`,
          node,
        )

      return this.makeClosure(declaration, new Env())
    }

    if (declaration.kind === K.VariableDeclaration) {
      const list = declaration.parent
      const moduleLevel =
        list.kind === K.VariableDeclarationList &&
        list.parent.kind === K.VariableStatement &&
        list.parent.parent.kind === K.SourceFile

      if (!moduleLevel)
        throw new Unsupported(
          `\`${node.text}\` is a local variable that is not available here`,
          node,
        )

      if (!(list.flags & NodeFlags.Const))
        throw new Unsupported(`\`${node.text}\` is a mutable module variable`, node)

      if (declaration.name.kind !== K.Identifier || !declaration.initializer)
        throw new Unsupported(`the declaration of \`${node.text}\` is not supported`, node)

      const early = this.loading.find(
        (entry) => entry.file === file.fileName && declaration.pos > entry.position,
      )

      if (early)
        throw new Unsupported(
          `\`${node.text}\` is read while its module is loading, before its own declaration has run, which throws`,
          node,
        )

      const known = this.constants.get(declaration)
      if (known) return known
      const saved = {
        pc: this.pc,
        stack: this.stack,
        instance: this.instance,
        cells: this.cells,
        frame: this.frame,
        assigned: this.assigned,
        epoch: this.epoch,
      }
      this.epoch = ++epochs
      this.pc = []
      this.stack = []
      this.instance = undefined
      this.cells = []
      this.frame = 0
      this.assigned = []
      this.loading.push({ file: file.fileName, position: declaration.pos })

      try {
        const value = this.evalExpr(declaration.initializer, new Env())

        if (
          value.k !== 'scalar' &&
          value.k !== 'rat' &&
          value.k !== 'float' &&
          value.k !== 'closure'
        )
          this.assertStable(file, declaration, value, node)

        this.constants.set(declaration, value)
        return value
      } finally {
        this.loading.pop()
        Object.assign(this, saved)
      }
    }

    if (declaration.kind === K.EnumDeclaration) {
      const decls = (symbol.declarations as readonly N[])
        .map((d) => d.resolve())
        .filter((d: N) => d.kind === K.EnumDeclaration)

      if (decls.some((d) => d.parent.kind !== K.SourceFile || d.getSourceFile() !== file)) {
        throw new Unsupported(
          `\`${node.text}\` is a local or cross-file merged enum that is not supported`,
          node,
        )
      }

      const lastPos = Math.max(...decls.map((d) => d.pos as number))
      const early = this.loading.find(
        (entry) => entry.file === file.fileName && lastPos > entry.position,
      )

      if (early)
        throw new Unsupported(
          `\`${node.text}\` is read while its module is loading, before its own declaration has run, which throws`,
          node,
        )

      const known = this.constants.get(declaration)
      if (known) return known
      const fields = new Map<string, Value>()

      for (const decl of decls) {
        const isConst = decl.modifiers?.some((m: N) => m.kind === K.ConstKeyword) === true

        for (const member of decl.members as readonly N[]) {
          if (member.name.kind !== K.Identifier && member.name.kind !== K.StringLiteral) {
            throw new Unsupported('computed enum member names are not supported', member)
          }

          const val = this.checker.getConstantValue(member)

          if (typeof val !== 'string' && (typeof val !== 'number' || !Number.isSafeInteger(val))) {
            throw new Unsupported(
              'only enums with constant whole-number or string values are supported',
              member,
            )
          }

          const key = member.name.text as string

          if (key === '__proto__')
            throw new Unsupported('`__proto__` as an enum member is not modeled', member)

          fields.set(
            key,
            typeof val === 'string'
              ? scalar(ir.lit(this.wellFormed(val, member)))
              : scalar(ir.lit(BigInt(val)), true),
          )

          if (!isConst && typeof val === 'number')
            fields.set(String(val), scalar(ir.lit(this.wellFormed(key, member))))
        }
      }

      const value: Value = { k: 'record', fields }
      this.assertStable(file, declaration, value, node)
      this.constants.set(declaration, value)
      return value
    }

    throw new Unsupported(
      `\`${node.text}\` is declared in a way that is not supported (only functions, const values and enums are)`,
      node,
    )
  }

  private assertStable(file: SourceFile, declaration: N, value: Value, use: Node) {
    const name = declaration.name.text as string
    const key = `${file.fileName}\0${name}`
    if (this.mutationChecked.has(key)) return

    const refuse = (reason: string, at: N): never => {
      throw new Unsupported(
        `\`${name}\` ${reason} at line ${locate(at).line} of its module, so its initial value cannot be assumed`,
        use,
      )
    }

    this.assertBuiltinsIntact(use)
    const loose = (file.statements as readonly N[]).find(
      (statement) => !tables().moduleDecl.has(statement.kind),
    )
    if (loose) refuse('shares its module with a statement that runs on load', loose)

    const isFunction = (node: N) =>
      node.kind === K.ArrowFunction ||
      node.kind === K.FunctionExpression ||
      node.kind === K.FunctionDeclaration ||
      node.kind === K.MethodDeclaration ||
      node.kind === K.GetAccessor ||
      node.kind === K.SetAccessor ||
      node.kind === K.Constructor

    const unwrap = (node: N): N => {
      while (
        node.kind === K.ParenthesizedExpression ||
        node.kind === K.AsExpression ||
        node.kind === K.SatisfiesExpression ||
        node.kind === K.NonNullExpression
      )
        node = node.expression

      return node
    }

    const local = new Set<string>()

    for (const statement of file.statements as readonly N[]) {
      if (statement.kind === K.FunctionDeclaration && statement.name) local.add(statement.name.text)

      if (statement.kind === K.VariableStatement) {
        for (const d of statement.declarationList.declarations as N[]) {
          if (d.name.kind === K.Identifier && d.initializer && isFunction(unwrap(d.initializer)))
            local.add(d.name.text)
        }
      }
    }

    const _isLocalCode = (node: N) => {
      const inner = unwrap(node)
      return isFunction(inner) || (inner.kind === K.Identifier && local.has(inner.text))
    }

    const imported = new Set<string>()

    for (const statement of file.statements as readonly N[]) {
      const clause = statement.kind === K.ImportDeclaration ? statement.importClause : undefined
      if (clause?.name) imported.add(clause.name.text)

      if (clause?.namedBindings?.kind === K.NamespaceImport)
        imported.add(clause.namedBindings.name.text)

      if (clause?.namedBindings?.kind === K.NamedImports)
        for (const element of clause.namedBindings.elements as N[]) imported.add(element.name.text)
    }

    const fromPackage = (callee: N): boolean => {
      let root = unwrap(callee)

      while (
        root.kind === K.PropertyAccessExpression ||
        root.kind === K.ElementAccessExpression ||
        root.kind === K.CallExpression
      )
        root = unwrap(root.expression)

      if (root.kind !== K.Identifier || !imported.has(root.text)) return false
      let symbol = this.checker.getSymbolAtLocation(root)
      if (symbol && symbol.flags & SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol)
      const source = symbol?.declarations[0]?.resolve()?.getSourceFile()
      return !!source && this.program.isSourceFileFromExternalLibrary(source)
    }

    const shallow = (value: Value | undefined) =>
      value?.k === 'record'
        ? [...value.fields.values()].every((field) => field.k === 'scalar')
        : value?.k === 'array'
          ? value.items.every((item) => item.k === 'scalar')
          : false

    const declaredConst = ((): boolean => {
      if (!declaration.initializer) return false

      for (let node: N = declaration.initializer; ; node = node.expression) {
        if (node.kind === K.AsExpression) {
          const type = node.type as N

          if (
            type.kind === K.TypeReference &&
            type.typeName.kind === K.Identifier &&
            type.typeName.text === 'const' &&
            !type.typeArguments?.length
          )
            return true
        } else if (
          node.kind !== K.ParenthesizedExpression &&
          node.kind !== K.SatisfiesExpression &&
          node.kind !== K.NonNullExpression
        )
          return false
      }
    })()
    const handedOver: { at: N; inFunction: boolean }[] = []

    const visit = (node: N, inFunction: boolean) => {
      if (
        node.kind === K.Identifier &&
        node.text === name &&
        node !== declaration.name &&
        !(
          declaration.kind === K.EnumDeclaration &&
          node.parent?.kind === K.EnumDeclaration &&
          node.parent.name === node
        )
      ) {
        let top = node
        const path: (string | undefined)[] = []

        while (
          (top.parent.kind === K.PropertyAccessExpression ||
            top.parent.kind === K.ElementAccessExpression) &&
          top.parent.expression === top
        ) {
          top = top.parent
          path.push(
            top.kind === K.PropertyAccessExpression
              ? top.name.text
              : top.argumentExpression.kind === K.StringLiteral ||
                  top.argumentExpression.kind === K.NumericLiteral
                ? top.argumentExpression.text
                : undefined,
          )
        }

        let outer = top

        while (
          outer.parent.kind === K.ParenthesizedExpression ||
          outer.parent.kind === K.AsExpression ||
          outer.parent.kind === K.SatisfiesExpression ||
          outer.parent.kind === K.NonNullExpression
        )
          outer = outer.parent

        const parent = outer.parent
        const assigned =
          parent.kind === K.BinaryExpression &&
          parent.left === outer &&
          parent.operatorToken.kind >= K.FirstAssignment &&
          parent.operatorToken.kind <= K.LastAssignment
        const updated =
          (parent.kind === K.PrefixUnaryExpression || parent.kind === K.PostfixUnaryExpression) &&
          (parent.operator === K.PlusPlusToken || parent.operator === K.MinusMinusToken)
        const called =
          parent.kind === K.CallExpression &&
          parent.expression === outer &&
          top.kind === K.PropertyAccessExpression

        if (
          assigned ||
          updated ||
          parent.kind === K.DeleteExpression ||
          (called && ARRAY_MUTATORS.has(top.name.text))
        )
          refuse('is modified', parent)

        let reached: Value[] = [value]

        for (const step of path.slice(0, called ? -1 : undefined)) {
          reached = reached.flatMap((part) => {
            if (step === 'length' && part.k === 'array')
              return [scalar(ir.lit(BigInt(part.items.length)), true)]

            const children =
              part.k === 'record'
                ? [...part.fields]
                : part.k === 'array'
                  ? part.items.map((item, i) => [String(i), item] as [string, Value])
                  : []
            return children
              .filter(([key]) => step === undefined || key === step)
              .map(([, child]) => child)
          })
        }

        const plain = reached.length > 0 && reached.every((part) => part.k === 'scalar')
        const flat = reached.length > 0 && reached.every(shallow)
        const compares =
          parent.kind === K.BinaryExpression &&
          [
            K.EqualsEqualsEqualsToken,
            K.ExclamationEqualsEqualsToken,
            K.EqualsEqualsToken,
            K.ExclamationEqualsToken,
            K.InKeyword,
          ].includes(parent.operatorToken.kind)

        const safeCallback = (callNode: N, methodName: string): boolean => {
          const cb = callNode.arguments?.[0] ? unwrap(callNode.arguments[0]) : undefined
          if (!cb || (cb.kind !== K.ArrowFunction && cb.kind !== K.FunctionExpression)) return false
          const maxParams = methodName === 'reduce' || methodName === 'reduceRight' ? 3 : 2
          const params = parametersOf(cb)
          if (params.length > maxParams || params.some((p) => p.dotDotDotToken)) return false

          if (cb.kind === K.FunctionExpression) {
            let usesArgs = false

            const scan = (n: N) => {
              if (usesArgs) return

              if (n.kind === K.Identifier && n.text === 'arguments') {
                usesArgs = true
                return
              }

              if (n !== cb && (n.kind === K.FunctionExpression || n.kind === K.FunctionDeclaration))
                return

              n.forEachChild(scan)
            }

            if (cb.body) scan(cb.body)
            if (usesArgs) return false
          }

          return true
        }

        const reads =
          (called &&
            flat &&
            (READING_METHODS.has(top.name.text) ||
              (CALLBACK_READING_METHODS.has(top.name.text) &&
                safeCallback(parent, top.name.text)))) ||
          (!called && plain) ||
          parent.kind === K.TypeQuery ||
          parent.kind === K.TypeOfExpression ||
          parent.kind === K.ExportSpecifier ||
          parent.kind === K.ExportAssignment ||
          ((parent.kind === K.SpreadElement ||
            parent.kind === K.SpreadAssignment ||
            (parent.kind === K.ForOfStatement && parent.expression === outer)) &&
            flat) ||
          compares
        const toLibrary =
          declaredConst &&
          parent.kind === K.CallExpression &&
          parent.expression !== outer &&
          fromPackage(parent.expression)
        const callee =
          (parent.kind === K.CallExpression || parent.kind === K.NewExpression) &&
          parent.expression !== outer
            ? parent.expression.getText(file)
            : ''
        const toReader =
          READERS.test(callee) ||
          (flat &&
            (SHALLOW_READERS.test(callee) ||
              (parent.kind === K.NewExpression && /^(Set|Map)$/.test(callee))))
        if (!reads && !toLibrary && !toReader) handedOver.push({ at: parent, inFunction })
      }

      node.forEachChild((child: N) => visit(child, inFunction || isFunction(child)))
    }

    visit(file, false)
    const atLoad = handedOver.find((entry) => !entry.inFunction)
    if (atLoad) refuse('is handed to other code while its module loads', atLoad.at)
    const inCode = handedOver.find((entry) => entry.inFunction)

    if (inCode)
      refuse('is handed to other code by a function, which may run before the law does,', inCode.at)

    this.mutationChecked.add(key)
  }
}

function isObject(value: Value): boolean {
  return (
    value.k === 'record' ||
    value.k === 'array' ||
    value.k === 'list' ||
    value.k === 'closure' ||
    value.k === 'map' ||
    value.k === 'set' ||
    value.k === 'iterator'
  )
}

function inOptionalChain(node: N): boolean {
  for (;;) {
    if (
      node.kind !== K.NonNullExpression &&
      node.kind !== K.PropertyAccessExpression &&
      node.kind !== K.ElementAccessExpression &&
      node.kind !== K.CallExpression
    )
      return false

    if (node.kind !== K.NonNullExpression && node.questionDotToken) return true
    node = node.expression
  }
}

function parametersOf(fn: N): N[] {
  return (fn.parameters as N[]).filter(
    (parameter) => !(parameter.name.kind === K.Identifier && parameter.name.text === 'this'),
  )
}

function boundNames(pattern: N, into: string[] = []): string[] {
  if (pattern.kind === K.Identifier) into.push(pattern.text)
  else
    for (const element of (pattern.elements ?? []) as N[])
      if (element.name) boundNames(element.name, into)

  return into
}

function canExit(node: N | undefined): boolean {
  if (!node) return false

  if (
    node.kind === K.ReturnStatement ||
    node.kind === K.ThrowStatement ||
    node.kind === K.BreakStatement ||
    node.kind === K.ContinueStatement
  )
    return true

  if (
    node.kind === K.ArrowFunction ||
    node.kind === K.FunctionExpression ||
    node.kind === K.FunctionDeclaration
  )
    return false

  return node.forEachChild((child: N) => canExit(child) || undefined) === true
}

function collectNames(target: N, into: Set<string>) {
  if (target.kind === K.Identifier) into.add(target.text)
  else if (target.kind === K.ParenthesizedExpression) collectNames(target.expression, into)
}
