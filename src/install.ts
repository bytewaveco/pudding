// Download the Lean release Pudding was built against, and keep the part of it Pudding uses.

import { execFileSync, spawn, spawnSync } from "node:child_process"
import { createHash } from "node:crypto"
import { copyFileSync, createReadStream, createWriteStream, existsSync, mkdirSync, readFileSync, readdirSync, renameSync, rmSync } from "node:fs"
import { homedir } from "node:os"
import { join } from "node:path"
import { Readable, Transform } from "node:stream"
import { pipeline } from "node:stream/promises"
import type { ReadableStream as WebStream } from "node:stream/web"
import { createZstdDecompress } from "node:zlib"
import { FALLBACK_IMPORTS } from "./lean.ts"

export const LEAN_VERSION = "4.36.0"

/** SHA-256 of each release archive, so that what gets installed is the Lean that Pudding was tested with. */
const CHECKSUMS: Record<string, string> = {
  "lean-4.36.0-darwin_aarch64": "49acada8749ad1343eff1224a3d2510ac61ed53363d37b5e738e8c587e7deabd",
  "lean-4.36.0-darwin": "476f9dcf7bee6a070e39a6b15cab7ada48b0086bd91d6e61aa1a454d3da409ce",
  "lean-4.36.0-linux": "2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb",
  "lean-4.36.0-linux_aarch64": "35471998152191ef809418ce5bf61f8fc5f209e5e3be05b48bdc4949fdb3e726",
}

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

/** Download a file, showing how far along it is when someone is watching, and return its SHA-256. */
async function download(url: string, file: string): Promise<string> {
  const response = await fetch(url)
  if (!response.ok || !response.body) throw new Error(`could not download ${url}: ${response.status} ${response.statusText}`)
  const total = Number(response.headers.get("content-length")) || 0
  const hash = createHash("sha256")
  const live = process.stderr.isTTY && total > 0
  let received = 0
  let shown = -1
  const meter = new Transform({
    transform(chunk: Buffer, _encoding, done) {
      hash.update(chunk)
      received += chunk.length
      const percent = Math.floor((received / total) * 100)
      if (live && percent !== shown) process.stderr.write(`\r  ${(shown = percent)}% of ${Math.round(total / 1e6)} MB`)
      done(null, chunk)
    },
  })
  try {
    await pipeline(Readable.fromWeb(response.body as WebStream), meter, createWriteStream(file))
  } finally {
    if (live) process.stderr.write("\r\x1b[K")
  }
  return hash.digest("hex")
}

/** Unpack a `.tar.zst`. Node does the decompression, so the machine's `tar` does not have to know zstd. */
async function unpack(archive: string, into: string): Promise<void> {
  const tar = spawn("tar", ["-xf", "-", "-C", into], { stdio: ["pipe", "inherit", "inherit"] })
  const exit = new Promise<number | null>((done, fail) => tar.on("close", done).on("error", fail))
  await pipeline(createReadStream(archive), createZstdDecompress(), tar.stdin)
  if ((await exit) !== 0) throw new Error("could not unpack the archive")
}

/**
 * Install Lean into the machine-wide cache, or into `<cwd>/.toolchain` when
 * `local` is set. By default everything Pudding does not use is removed after
 * unpacking; `full` keeps the whole toolchain, which a proof you write
 * yourself may need.
 */
export async function installLean(cwd: string, options: { full: boolean; local: boolean; log: (line: string) => void }): Promise<string> {
  const name = toolchainName()
  if (!name) throw new Error(`there is no prebuilt Lean for ${process.platform}-${process.arch}; install Lean ${LEAN_VERSION} yourself and set PUDDING_LEAN`)
  const root = options.local ? join(cwd, ".toolchain") : cacheDirectory()
  const target = join(root, name)
  const binary = join(target, "bin", "lean")
  // The compiler's own library is the first thing trimming removes, so it tells a whole toolchain from a trimmed one.
  const whole = existsSync(join(target, "lib", "lean", "Lean.olean"))
  if (existsSync(binary) && (whole || !options.full)) {
    options.log(`Lean ${LEAN_VERSION} is already installed at ${target}`)
    return binary
  }
  const url = `https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/${name}.tar.zst`
  options.log(`Downloading ${url}`)
  // Everything happens in a directory of its own and is moved into place at
  // the end, so an interrupted install never looks like a finished one.
  const staging = join(root, `.installing-${process.pid}`)
  rmSync(staging, { recursive: true, force: true })
  mkdirSync(staging, { recursive: true })
  try {
    const archive = join(staging, `${name}.tar.zst`)
    const found = await download(url, archive)
    if (found !== CHECKSUMS[name]) {
      throw new Error(`the download does not match the Lean ${LEAN_VERSION} release: expected SHA-256 ${CHECKSUMS[name]}, found ${found}`)
    }
    options.log("Unpacking")
    await unpack(archive, staging)
    if (!options.full) prune(join(staging, name))
    const stagedBinary = join(staging, name, "bin", "lean")
    const versionText = execFileSync(stagedBinary, ["--version"], { encoding: "utf8" }).trim()
    rmSync(target, { recursive: true, force: true })
    renameSync(join(staging, name), target)
    options.log(`Installed ${versionText}`)
  } finally {
    rmSync(staging, { recursive: true, force: true })
  }
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
  // Strip local symbols from the kept binary and shared libraries when the host tools are available.
  // Keep a backup of each file so a failed strip or macOS ad-hoc codesign never leaves a broken binary.
  const stripArgs = process.platform === "darwin" ? ["-x"] : process.platform === "linux" ? ["--strip-unneeded"] : undefined
  if (stripArgs) {
    const binaries = [join(target, "bin", "lean"), ...readdirSync(library).filter(name => /^lib(leanshared|Init_shared).*\.(dylib|so)$/.test(name)).map(name => join(library, name))]
    for (const file of binaries) {
      const backup = `${file}.orig`
      copyFileSync(file, backup)
      const stripped = spawnSync("strip", [...stripArgs, file], { stdio: "ignore" })
      const signedOk = stripped.status === 0 && (process.platform !== "darwin" || spawnSync("codesign", ["--force", "--sign", "-", file], { stdio: "ignore" }).status === 0)
      if (!signedOk) renameSync(backup, file)
      else rmSync(backup, { force: true })
    }
  }
}
