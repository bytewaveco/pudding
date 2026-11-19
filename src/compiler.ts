// The TypeScript 7 compiler API, loaded from whichever implementation the
// project has installed: `typescript` 7 itself, or `tsrs`, which publishes the
// same API. The project owns its compiler; Pudding does not bring one.

import { createRequire } from "node:module"
import { join } from "node:path"
import { pathToFileURL } from "node:url"

export type { Checker, Program, Type } from "typescript/unstable/sync"
export type { Node, SourceFile } from "typescript/unstable/ast"

type Sync = typeof import("typescript/unstable/sync")
type Ast = typeof import("typescript/unstable/ast")

// TypeScript 7.0 publishes the API under `unstable/`; 7.1 and tsrs do not.
const PROVIDERS = {
  typescript: ["typescript/unstable", "typescript"],
  tsrs: ["tsrs"],
}

type Name = keyof typeof PROVIDERS

interface Loaded {
  name: Name
  version: string
  sync: Sync
  ast: Ast
}

/**
 * Look next to Pudding first, where a package manager links a peer
 * dependency, and then in the project being checked, which covers a linked
 * or globally installed Pudding.
 */
async function load(names: Name[]): Promise<Loaded | undefined> {
  const bases = [import.meta.url, pathToFileURL(join(process.cwd(), "package.json")).href]
  for (const name of names) {
    for (const base of bases) {
      const require = createRequire(base)
      for (const entry of PROVIDERS[name]) {
        try {
          // TypeScript 6 and earlier resolve as a package but do not export this API.
          const sync = require.resolve(`${entry}/sync`)
          const ast = require.resolve(`${entry}/ast`)
          const version: unknown = require(`${name}/package.json`).version
          return {
            name,
            version: typeof version === "string" ? version : "unknown",
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

const requested = process.env["PUDDING_COMPILER"]
const names = Object.keys(PROVIDERS) as Name[]
const loaded = requested === undefined || requested === ""
  ? await load(names)
  : names.includes(requested as Name) ? await load([requested as Name]) : undefined

/** Which compiler was loaded, as reports name it. */
export const compiler = loaded ? `${loaded.name === "typescript" ? "TypeScript" : loaded.name} ${loaded.version}` : ""

/** Why no compiler could be loaded; `run` reports it instead of checking anything. */
export const compilerProblem = loaded
  ? undefined
  : requested === undefined || requested === ""
    ? "no TypeScript 7 compiler was found: install `typescript` 7 or `tsrs` in this project"
    : names.includes(requested as Name)
      ? `PUDDING_COMPILER names \`${requested}\`, which is not installed in this project, or is older than TypeScript 7`
      : `PUDDING_COMPILER must be one of ${names.map(name => `\`${name}\``).join(" or ")}, not \`${requested}\``

// Without a compiler these are empty, so that modules building tables from
// them still load; `run` stops at `compilerProblem` before any of it is used.
const missing = {} as never
const sync = loaded?.sync
const ast = loaded?.ast

export const API = sync?.API ?? missing
export const DiagnosticCategory = sync?.DiagnosticCategory ?? missing
export const ElementFlags = sync?.ElementFlags ?? missing
export const SignatureKind = sync?.SignatureKind ?? missing
export const SymbolFlags = sync?.SymbolFlags ?? missing
export const TypeFlags = sync?.TypeFlags ?? missing
export const NodeFlags = ast?.NodeFlags ?? missing
export const SyntaxKind = ast?.SyntaxKind ?? missing
