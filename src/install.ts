// Download the Lean toolchain Pudding was built against into `.toolchain/`.

import { execFileSync, spawnSync } from "node:child_process"
import { existsSync, mkdirSync, readFileSync, readdirSync, rmSync } from "node:fs"
import { homedir } from "node:os"
import { join } from "node:path"
import { FALLBACK_IMPORTS } from "./lean.ts"

export const LEAN_VERSION = "4.36.0"

/** Where downloads shared by every project on this machine are kept. */
export function cacheDirectory(): string {
  if (process.env["PUDDING_CACHE_DIR"]) return process.env["PUDDING_CACHE_DIR"]
  if (process.platform === "darwin") return join(homedir(), "Library", "Caches", "pudding")
  if (process.platform === "win32") return join(process.env["LOCALAPPDATA"] ?? join(homedir(), "AppData", "Local"), "pudding", "Cache")
  return join(process.env["XDG_CACHE_HOME"] ?? join(homedir(), ".cache"), "pudding")
}

/** The directory name of the Lean release for this machine, or undefined when there is no prebuilt one. */
export function toolchainName(): string | undefined {
  const names: Record<string, string> = {
    "darwin-arm64": "darwin_aarch64", "darwin-x64": "darwin", "linux-x64": "linux", "linux-arm64": "linux_aarch64",
  }
  const name = names[`${process.platform}-${process.arch}`]
  return name && `lean-${LEAN_VERSION}-${name}`
}

/**
 * Install Lean into the machine-wide cache, or into `<cwd>/.toolchain` when
 * `local` is set. By default everything Pudding does not use is removed after
 * unpacking; `full` keeps the whole toolchain, which a proof you write
 * yourself may need.
 */
export function installLean(cwd: string, options: { full: boolean; local: boolean; log: (line: string) => void }): string {
  const name = toolchainName()
  if (!name) throw new Error(`there is no prebuilt Lean for ${process.platform}-${process.arch}; install Lean ${LEAN_VERSION} yourself and set PUDDING_LEAN`)
  const root = options.local ? join(cwd, ".toolchain") : cacheDirectory()
  const target = join(root, name)
  const binary = join(target, "bin", "lean")
  if (existsSync(binary)) {
    options.log(`Lean ${LEAN_VERSION} is already installed at ${target}`)
    return binary
  }
  mkdirSync(root, { recursive: true })
  const url = `https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/${name}.tar.zst`
  options.log(`Downloading ${url}`)
  const archive = join(root, `${name}.tar.zst`)
  try {
    execFileSync("curl", ["-fL", "--progress-bar", "-o", archive, url], { stdio: "inherit" })
    const extracted = spawnSync("tar", ["--zstd", "-xf", archive, "-C", root], { stdio: "inherit" })
    if (extracted.status !== 0) throw new Error("could not unpack the archive; `tar` needs zstd support")
  } finally {
    rmSync(archive, { force: true })
  }
  if (!options.full) prune(target)
  options.log(`Installed ${execFileSync(binary, ["--version"], { encoding: "utf8" }).trim()}`)
  return binary
}

/** The modules a Lean source file imports, in any of the forms the module system allows. */
function headerImports(text: string): string[] {
  const imports: string[] = []
  for (const raw of text.replace(/\/-[\s\S]*?-\//g, "").replace(/--.*$/gm, "").split("\n")) {
    const line = raw.trim()
    if (!line || line === "module" || line === "prelude") continue
    const match = /^(?:public\s+)?(?:private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$/.exec(line)
    if (!match) break
    imports.push(...match[1]!.trim().split(/\s+/))
  }
  return imports
}

/** Every module the given ones import, directly or not, read from the sources a toolchain ships. */
export function importClosure(toolchain: string, roots: readonly string[]): string[] {
  const seen = new Set<string>()
  const stack = [...roots]
  while (stack.length) {
    const name = stack.pop()!
    if (seen.has(name)) continue
    seen.add(name)
    stack.push(...headerImports(readFileSync(join(toolchain, "src", "lean", ...name.split(".")) + ".lean", "utf8")))
  }
  return [...seen].sort()
}

/**
 * Remove everything from an unpacked toolchain except what running `lean` on
 * Pudding's theorems needs: the binary, its shared libraries, and the compiled
 * form of the modules those theorems import. That is about an eighth of the
 * download. `scripts/pack-runtime.mjs` goes further and strips the libraries.
 */
export function prune(target: string) {
  const library = join(target, "lib", "lean")
  const keep = new Set<string>()
  for (const name of importClosure(target, FALLBACK_IMPORTS)) {
    // A file that is not itself a `module` makes Lean open all three of these for each import.
    for (const variant of [".olean", ".olean.server", ".olean.private"]) keep.add(join(library, ...name.split(".")) + variant)
  }
  const visit = (directory: string) => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const path = join(directory, entry.name)
      if (entry.isDirectory()) {
        visit(path)
        if (!readdirSync(path).length) rmSync(path, { recursive: true })
      } else if (!keep.has(path)) rmSync(path)
    }
  }
  for (const entry of readdirSync(target)) {
    if (entry !== "bin" && entry !== "lib" && !entry.startsWith("LICENSE")) rmSync(join(target, entry), { recursive: true })
  }
  for (const entry of readdirSync(join(target, "bin"))) if (entry !== "lean") rmSync(join(target, "bin", entry), { recursive: true })
  for (const entry of readdirSync(join(target, "lib"))) if (entry !== "lean") rmSync(join(target, "lib", entry), { recursive: true })
  for (const entry of readdirSync(library, { withFileTypes: true })) {
    const path = join(library, entry.name)
    if (entry.isDirectory()) {
      visit(path)
      if (!readdirSync(path).length) rmSync(path, { recursive: true })
    } else if (!keep.has(path) && !/^lib(leanshared|Init_shared).*\.(dylib|so)$/.test(entry.name)) rmSync(path)
  }
}
