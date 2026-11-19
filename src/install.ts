// Download the Lean toolchain Pudding was built against into `.toolchain/`.

import { execFileSync, spawnSync } from "node:child_process"
import { existsSync, mkdirSync, readdirSync, rmSync } from "node:fs"
import { join } from "node:path"

export const LEAN_VERSION = "4.36.0"

function platform(): string {
  const key = `${process.platform}-${process.arch}`
  const names: Record<string, string> = {
    "darwin-arm64": "darwin_aarch64", "darwin-x64": "darwin", "linux-x64": "linux", "linux-arm64": "linux_aarch64",
  }
  const name = names[key]
  if (!name) throw new Error(`there is no prebuilt Lean for ${key}; install Lean ${LEAN_VERSION} yourself and set PUDDING_LEAN`)
  return name
}

/**
 * Install Lean under `<cwd>/.toolchain`. By default everything Pudding does
 * not use (the C toolchain, static libraries, sources, the `Std` and `Lean`
 * libraries) is removed, which keeps about a sixth of the download.
 */
export function installLean(cwd: string, options: { full: boolean; log: (line: string) => void }): string {
  const name = `lean-${LEAN_VERSION}-${platform()}`
  const root = join(cwd, ".toolchain")
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
