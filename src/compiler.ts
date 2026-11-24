import { createRequire } from 'node:module'
import { join } from 'node:path'
import { pathToFileURL } from 'node:url'

export type { Checker, Program, Type } from 'typescript/unstable/sync'
export type { Node, SourceFile } from 'typescript/unstable/ast'

type Sync = typeof import('typescript/unstable/sync')
type Ast = typeof import('typescript/unstable/ast')

const PROVIDERS = {
  typescript: ['typescript/unstable', 'typescript'],
  tsrs: ['tsrs'],
}

type Name = keyof typeof PROVIDERS

interface Loaded {
  name: Name
  version: string
  sync: Sync
  ast: Ast
}

async function load(names: Name[], cwd?: string): Promise<Loaded | undefined> {
  const roots = [import.meta.url]
  if (cwd) roots.push(pathToFileURL(join(cwd, 'package.json')).href)
  const current = pathToFileURL(join(process.cwd(), 'package.json')).href
  if (!roots.includes(current)) roots.push(current)

  for (const name of names) {
    for (const base of roots) {
      const require = createRequire(base)

      for (const entry of PROVIDERS[name]) {
        try {
          const sync = require.resolve(`${entry}/sync`)
          const ast = require.resolve(`${entry}/ast`)
          const version: unknown = require(`${name}/package.json`).version
          return {
            name,
            version: typeof version === 'string' ? version : 'unknown',
            sync: await import(pathToFileURL(sync).href),
            ast: await import(pathToFileURL(ast).href),
          }
        } catch {
          continue
        }
      }
    }
  }

  return undefined
}

const names = Object.keys(PROVIDERS) as Name[]
const missing = {} as never

function apply(found: Loaded | undefined, requested: string | undefined) {
  compiler = found
    ? `${found.name === 'typescript' ? 'TypeScript' : found.name} ${found.version}`
    : ''
  compilerProblem = found
    ? undefined
    : requested === undefined || requested === ''
      ? 'no TypeScript 7 compiler was found: install `typescript` 7 or `tsrs` in this project'
      : names.includes(requested as Name)
        ? `PUDDING_COMPILER names \`${requested}\`, which is not installed in this project, or is older than TypeScript 7`
        : `PUDDING_COMPILER must be one of ${names.map((name) => `\`${name}\``).join(' or ')}, not \`${requested}\``
  const sync = found?.sync
  const ast = found?.ast
  API = sync?.API ?? missing
  DiagnosticCategory = sync?.DiagnosticCategory ?? missing
  ElementFlags = sync?.ElementFlags ?? missing
  SignatureKind = sync?.SignatureKind ?? missing
  SymbolFlags = sync?.SymbolFlags ?? missing
  TypeFlags = sync?.TypeFlags ?? missing
  NodeFlags = ast?.NodeFlags ?? missing
  SyntaxKind = ast?.SyntaxKind ?? missing
}

export let compiler = ''

export let compilerProblem: string | undefined

export let API: Sync['API'] = missing
export let DiagnosticCategory: Sync['DiagnosticCategory'] = missing
export let ElementFlags: Sync['ElementFlags'] = missing
export let SignatureKind: Sync['SignatureKind'] = missing
export let SymbolFlags: Sync['SymbolFlags'] = missing
export let TypeFlags: Sync['TypeFlags'] = missing
export let NodeFlags: Ast['NodeFlags'] = missing
export let SyntaxKind: Ast['SyntaxKind'] = missing

const initialRequested = process.env['PUDDING_COMPILER']
const initialLoaded =
  initialRequested === undefined || initialRequested === ''
    ? await load(names)
    : names.includes(initialRequested as Name)
      ? await load([initialRequested as Name])
      : undefined
apply(initialLoaded, initialRequested)

export async function ensureCompiler(cwd?: string): Promise<void> {
  if (!compilerProblem) return
  const requested = process.env['PUDDING_COMPILER']
  const found =
    requested === undefined || requested === ''
      ? await load(names, cwd)
      : names.includes(requested as Name)
        ? await load([requested as Name], cwd)
        : undefined
  if (found) apply(found, requested)
}
