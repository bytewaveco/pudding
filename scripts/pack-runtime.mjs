#!/usr/bin/env node

import { execFileSync, spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import {
  copyFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  openSync,
  readFileSync,
  readSync,
  closeSync,
  readdirSync,
  rmSync,
  statSync,
  writeFileSync,
  chmodSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { basename, dirname, join, relative } from 'node:path'

import { FALLBACK_IMPORTS, FAST_IMPORTS } from '../dist/lean.js'

const PROFILES = { fast: FAST_IMPORTS, fallback: FALLBACK_IMPORTS, init: ['Init'] }
const FALLBACK_TACTIC = 'first | grind | (intros; simp_all; done) | (intros; simp_all <;> omega)'
const OLEAN_VARIANTS = ['.olean', '.olean.server', '.olean.private']

function fail(message) {
  console.error(`pack-runtime: ${message}`)
  process.exit(1)
}

function parseArgs(argv) {
  const options = {
    profile: 'fallback',
    imports: [],
    strip: true,
    smoke: true,
    force: false,
    package: false,
    build: 0,
    positional: [],
  }

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i]

    if (arg === '--profile') options.profile = argv[++i]
    else if (arg === '--imports') options.imports.push(...argv[++i].split(',').filter(Boolean))
    else if (arg === '--package') options.package = true
    else if (arg === '--build') options.build = Number(argv[++i])
    else if (arg === '--no-strip') options.strip = false
    else if (arg === '--no-smoke') options.smoke = false
    else if (arg === '--force') options.force = true
    else if (arg === '-h' || arg === '--help') {
      const lines = readFileSync(new URL(import.meta.url), 'utf8')
        .split('\n')
        .slice(1)
      console.log(
        lines
          .slice(
            0,
            lines.findIndex((l) => !l.startsWith('//')),
          )
          .map((l) => l.replace(/^\/\/ ?/, ''))
          .join('\n'),
      )
      process.exit(0)
    } else if (arg.startsWith('--')) fail(`unknown option ${arg}`)
    else options.positional.push(arg)
  }

  if (options.positional.length !== 2)
    fail(
      'usage: node pack-runtime.mjs <toolchain dir> <output dir> [--profile fallback|fast|init] [--imports A,B] [--no-strip] [--no-smoke] [--force]',
    )

  if (!Number.isInteger(options.build) || options.build < 0 || options.build > 99)
    fail('--build takes a number from 0 to 99')

  if (!PROFILES[options.profile])
    fail(`unknown profile ${options.profile}; use fallback, fast or init`)

  return options
}

export function headerImports(text) {
  const imports = []
  text = text.replace(/\/-[\s\S]*?-\//g, '').replace(/--.*$/gm, '')

  for (const raw of text.split('\n')) {
    const line = raw.trim()
    if (!line || line === 'module' || line === 'prelude') continue
    const match = /^(?:public\s+)?(?:private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$/.exec(line)
    if (!match) break
    imports.push(...match[1].trim().split(/\s+/))
  }

  return imports
}

export function importClosure(srcRoot, roots) {
  const seen = new Set()
  const stack = [...roots]

  while (stack.length) {
    const name = stack.pop()
    if (seen.has(name)) continue
    seen.add(name)
    const file = join(srcRoot, ...name.split('.')) + '.lean'
    if (!existsSync(file)) fail(`module ${name} has no source at ${file}`)
    stack.push(...headerImports(readFileSync(file, 'utf8')))
  }

  return [...seen].sort()
}

function readHead(file, length) {
  const fd = openSync(file, 'r')

  try {
    const buffer = Buffer.alloc(Math.min(length, statSync(file).size))
    readSync(fd, buffer, 0, buffer.length, 0)
    return buffer
  } finally {
    closeSync(fd)
  }
}

function binaryFormat(file) {
  const head = readHead(file, 4)
  if (head.length < 4) return undefined
  const magic = head.readUInt32LE(0)

  if (magic === 0xfeedfacf || magic === 0xfeedface || magic === 0xcafebabe || magic === 0xbebafeca)
    return 'macho'

  if (head[0] === 0x7f && head[1] === 0x45 && head[2] === 0x4c && head[3] === 0x46) return 'elf'
  return undefined
}

function machoNeeded(file) {
  const buffer = readFileSync(file)

  if (buffer.readUInt32LE(0) !== 0xfeedfacf)
    fail(`${file}: only thin 64-bit Mach-O files are supported`)

  const ncmds = buffer.readUInt32LE(16)
  const needed = []
  let offset = 32

  for (let i = 0; i < ncmds; i++) {
    const cmd = buffer.readUInt32LE(offset) & 0x7fffffff
    const size = buffer.readUInt32LE(offset + 4)

    if ([0xc, 0x18, 0x1f, 0x20, 0x23].includes(cmd)) {
      const nameOffset = buffer.readUInt32LE(offset + 8)
      const end = buffer.indexOf(0, offset + nameOffset)
      needed.push(buffer.toString('utf8', offset + nameOffset, end))
    }

    offset += size
  }

  return needed
}

function elfNeeded(file) {
  const b = readFileSync(file)
  const is64 = b[4] === 2
  const le = b[5] === 1
  const u16 = (o) => (le ? b.readUInt16LE(o) : b.readUInt16BE(o))
  const u32 = (o) => (le ? b.readUInt32LE(o) : b.readUInt32BE(o))
  const word = (o) => (is64 ? Number(le ? b.readBigUInt64LE(o) : b.readBigUInt64BE(o)) : u32(o))
  const phoff = word(is64 ? 32 : 28)
  const phentsize = u16(is64 ? 54 : 42)
  const phnum = u16(is64 ? 56 : 44)
  const segments = []
  let dynamic

  for (let i = 0; i < phnum; i++) {
    const p = phoff + i * phentsize
    const type = u32(p)
    const seg = is64
      ? { offset: word(p + 8), vaddr: word(p + 16), filesz: word(p + 32) }
      : { offset: u32(p + 4), vaddr: u32(p + 8), filesz: u32(p + 16) }
    if (type === 1) segments.push(seg)
    if (type === 2) dynamic = seg
  }

  if (!dynamic) return []

  const toOffset = (vaddr) => {
    const seg = segments.find((s) => vaddr >= s.vaddr && vaddr < s.vaddr + s.filesz)
    return seg ? vaddr - seg.vaddr + seg.offset : undefined
  }

  const entrySize = is64 ? 16 : 8
  const neededOffsets = []
  let strtab

  for (let p = dynamic.offset; p < dynamic.offset + dynamic.filesz; p += entrySize) {
    const tag = word(p)
    const value = word(p + (is64 ? 8 : 4))
    if (tag === 0) break
    if (tag === 1) neededOffsets.push(value)
    if (tag === 5) strtab = toOffset(value)
  }

  if (strtab === undefined) return []
  return neededOffsets.map((o) => b.toString('utf8', strtab + o, b.indexOf(0, strtab + o)))
}

function neededLibraries(file) {
  const format = binaryFormat(file)
  if (format === 'macho') return machoNeeded(file)
  if (format === 'elf') return elfNeeded(file)
  return []
}

function toolchainLibraries(toolchain, binary) {
  const searchDirs = [
    join(toolchain, 'lib', 'lean'),
    join(toolchain, 'lib'),
    join(toolchain, 'bin'),
  ]
  const found = new Map()
  const stack = [binary]

  while (stack.length) {
    for (const name of neededLibraries(stack.pop())) {
      const base = basename(name)
      if (found.has(base)) continue
      const dir = searchDirs.find((d) => existsSync(join(d, base)))
      if (!dir) continue
      const path = join(dir, base)
      found.set(base, path)
      stack.push(path)
    }
  }

  return [...found.values()]
}

function hostFormat() {
  return process.platform === 'darwin' ? 'macho' : process.platform === 'linux' ? 'elf' : undefined
}

function has(tool) {
  return (
    spawnSync(tool, ['--version'], { stdio: 'ignore' }).error === undefined ||
    spawnSync('which', [tool], { stdio: 'ignore' }).status === 0
  )
}

function strip(file, notes) {
  const format = binaryFormat(file)
  if (!format) return

  if (format !== hostFormat()) {
    notes.add(`not stripped: ${format} binaries cannot be stripped on this host`)
    return
  }

  if (!has('strip')) {
    notes.add('not stripped: no `strip` on PATH')
    return
  }

  const args = format === 'macho' ? ['-x', file] : ['--strip-unneeded', file]
  const result = spawnSync('strip', args, { encoding: 'utf8' })
  if (result.status !== 0) fail(`strip ${args.join(' ')} failed: ${result.stderr}`)

  if (format === 'macho') {
    const signed = spawnSync('codesign', ['--force', '--sign', '-', file], { encoding: 'utf8' })
    if (signed.status !== 0) fail(`codesign failed on ${file}: ${signed.stderr}`)
  }
}

function copy(from, to) {
  mkdirSync(dirname(to), { recursive: true })
  copyFileSync(from, to)
  chmodSync(to, statSync(from).mode)
}

function walk(dir) {
  const out = []

  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name)

    if (entry.isDirectory()) out.push(...walk(path))
    else out.push(path)
  }

  return out
}

function smokeTest(out, imports, strong) {
  const lean = join(out, 'bin', 'lean')
  const probe = spawnSync(lean, ['--version'], { encoding: 'utf8' })
  if (probe.status !== 0) return 'skipped: the packed lean does not run on this host'
  const dir = mkdtempSync(join(tmpdir(), 'pack-runtime-'))

  try {
    const file = join(dir, 'Smoke.lean')
    writeFileSync(
      file,
      [
        'prelude',
        ...imports.map((m) => `import ${m}`),
        'theorem s0 : (["a", "b"].all fun x => (x ++ "!" == x) == false) = true := by decide +kernel',
        'theorem s1 (x : Int) : (decide (x < x + 1)) = true := by grind',
        ...(strong
          ? [
              `theorem s2 (x : String) : (!((x ++ "a") == "")) = true := by ${FALLBACK_TACTIC}`,
              `theorem s3 (x0 : Int) (x1 : Int) : (((-x1) == x1) && (decide (x0 ≤ x0))) = true → (!(decide ((Int.tmod (10 : Int) x0) < (x1 - x1)))) = true := by ${FALLBACK_TACTIC}`,
            ]
          : []),
        '',
      ].join('\n'),
    )
    const result = spawnSync(lean, ['--json', file], { encoding: 'utf8' })
    if (result.status !== 0) fail(`smoke test failed:\n${result.stdout}${result.stderr}`)
    return `passed (${probe.stdout.trim()})`
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

function main() {
  const options = parseArgs(process.argv.slice(2))
  const [toolchain, out] = options.positional
  const exe = ['lean', 'lean.exe'].map((n) => join(toolchain, 'bin', n)).find(existsSync)
  if (!exe) fail(`no bin/lean in ${toolchain}`)
  if (exe.endsWith('.exe')) fail('Windows toolchains are not supported')
  const srcRoot = join(toolchain, 'src', 'lean')
  const libRoot = join(toolchain, 'lib', 'lean')

  if (!existsSync(join(srcRoot, 'Init.lean')))
    fail(`no Lean sources at ${srcRoot}; they are needed to compute the import closure`)

  if (existsSync(out)) {
    if (!options.force) fail(`${out} exists; pass --force to replace it`)
    rmSync(out, { recursive: true, force: true })
  }

  const notes = new Set()

  const outExe = join(out, 'bin', 'lean')
  copy(exe, outExe)
  const libraries = toolchainLibraries(toolchain, exe)

  if (!libraries.length)
    notes.add('the binary loads no library from the toolchain; it may be statically linked')

  for (const lib of libraries) copy(lib, join(out, relative(toolchain, lib)))

  if (options.strip)
    for (const file of [outExe, ...libraries.map((lib) => join(out, relative(toolchain, lib)))])
      strip(file, notes)

  const roots = [...PROFILES[options.profile], ...options.imports]
  const modules = importClosure(srcRoot, roots)

  for (const name of modules) {
    const stem = join(...name.split('.'))
    let copied = 0

    for (const variant of OLEAN_VARIANTS) {
      const from = join(libRoot, stem + variant)

      if (existsSync(from)) {
        copy(from, join(out, 'lib', 'lean', stem + variant))
        copied++
      } else if (variant === '.olean') fail(`missing ${from}`)
    }

    if (copied < OLEAN_VARIANTS.length)
      notes.add(
        'some modules have no .olean.server/.olean.private (a toolchain before the module system?)',
      )
  }

  for (const entry of readdirSync(toolchain))
    if (entry.startsWith('LICENSE')) {
      const from = join(toolchain, entry)
      if (statSync(from).isFile()) copy(from, join(out, entry))
    }

  const files = walk(out)
    .sort()
    .map((path) => ({
      path: relative(out, path),
      size: statSync(path).size,
      sha256: createHash('sha256').update(readFileSync(path)).digest('hex'),
    }))
  const version = (() => {
    try {
      return execFileSync(outExe, ['--version'], { encoding: 'utf8' }).trim()
    } catch {
      return basename(toolchain)
    }
  })()
  const smoke = options.smoke
    ? smokeTest(out, roots, options.profile !== 'fast')
    : 'skipped (--no-smoke)'
  const manifest = {
    lean: version,
    source: basename(toolchain),
    profile: options.profile,
    roots,
    modules: modules.length,
    stripped: options.strip,
    notes: [...notes],
    smoke,
    totalSize: files.reduce((s, f) => s + f.size, 0),
    files,
  }
  writeFileSync(join(out, 'manifest.json'), JSON.stringify(manifest, null, 2) + '\n')

  if (options.package) {
    const tag = basename(toolchain).replace(/^lean-[^-]+-/, '')
    const os = tag.startsWith('darwin') ? 'darwin' : tag.startsWith('linux') ? 'linux' : undefined
    if (!os) fail(`cannot tell the platform of ${basename(toolchain)}`)
    const cpu = tag.endsWith('aarch64') ? 'arm64' : 'x64'
    const pudding = JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8'))
    const [major, minor, patch] = basename(toolchain).split('-')[1].split('.').map(Number)
    writeFileSync(
      join(out, 'package.json'),
      JSON.stringify(
        {
          name: `${pudding.name}-lean-${os}-${cpu}`,
          version: `${major}.${minor}.${patch * 100 + options.build}`,
          description: `The part of Lean ${major}.${minor}.${patch} that Pudding uses, for ${os} ${cpu}`,
          license: 'Apache-2.0',
          repository: pudding.repository,
          os: [os],
          cpu: [cpu],
          preferUnplugged: true,
          files: ['bin', 'lib', 'LICENSE', 'LICENSES', 'manifest.json'],
        },
        null,
        2,
      ) + '\n',
    )
  }

  console.log(
    `packed ${files.length} files, ${(manifest.totalSize / 1e6).toFixed(1)} MB, ${modules.length} modules (${options.profile}) into ${out}`,
  )
  for (const note of notes) console.log(`note: ${note}`)
  console.log(`smoke test: ${smoke}`)
}

main()
