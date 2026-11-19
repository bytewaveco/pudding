// Download the Lean toolchain Pudding was built against into `.toolchain/`.

import { execFileSync, spawnSync } from "node:child_process"
import { existsSync, mkdirSync, readdirSync, rmSync } from "node:fs"
import { homedir } from "node:os"
import { join } from "node:path"

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
 * `local` is set. By default everything Pudding does not use (the C
 * toolchain, static libraries, sources, the `Std` and `Lean` libraries) is
 * removed after unpacking.
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

/** Remove everything from an unpacked toolchain except what running `lean` on Pudding's theorems needs. */
export function prune(target: string) {
  for (const entry of readdirSync(target)) {
    if (entry !== "bin" && entry !== "lib" && !entry.startsWith("LICENSE")) rmSync(join(target, entry), { recursive: true })
  }
  for (const entry of readdirSync(join(target, "bin"))) if (entry !== "lean") rmSync(join(target, "bin", entry), { recursive: true })
  for (const entry of readdirSync(join(target, "lib"))) if (entry !== "lean") rmSync(join(target, "lib", entry), { recursive: true })
  for (const entry of readdirSync(join(target, "lib", "lean"))) {
    const keep = entry === "Init" || entry.startsWith("Init.") || /^lib(leanshared|Init_shared).*\.(dylib|so)$/.test(entry)
    if (!keep) rmSync(join(target, "lib", "lean", entry), { recursive: true })
  }
}
