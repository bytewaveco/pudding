<h1 align="center"><img alt="Pudding" src="assets/header.png" width="440"></h1>

<p align="center"><b>Laws for TypeScript, written like Vitest tests and proved by Lean 4 for every input.</b></p>

<p align="center">
  <a href="#quick-start">Quick start</a> ·
  <a href="#runs-in-vitest">Vitest</a> ·
  <a href="#checked-by-lean-4">Lean</a> ·
  <a href="#writing-laws">Writing laws</a> ·
  <a href="#what-it-can-prove">What it can prove</a> ·
  <a href="#how-it-works">How it works</a> ·
  <a href="#what-a-proof-means">What a proof means</a>
</p>

A test checks the inputs you thought of. A law leaves the inputs open. You
give their types, and Pudding proves the expectation for every value of those
types, against the functions you already have. A law file is ordinary
TypeScript and an ordinary Vitest test file, and
[Lean 4](https://lean-lang.org) checks each proof. A law that is false fails
with the input that breaks it.

## The bug a test missed

This function counts the pages of a list.

```ts
// pages.ts
export function pageCount(items: number, perPage: number): number {
  return Math.floor(items / perPage) + 1
}
```

Its unit test passes, because 25 is not a multiple of 10.

```ts
// pages.test.ts
test("25 items at 10 a page take 3 pages", () => {
  expect(pageCount(25, 10)).toBe(3)
})
```

A law says what must hold for any number of items at any page size.

```ts
// pages.law.ts
import { domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { pageCount } from "./pages"

type Items = Integer<1, 1_000_000>
type PerPage = Integer<1, 100>

law("every item is on a page", domain<[Items, PerPage]>(), ([items, perPage]) => {
  expect(pageCount(items, perPage) * perPage >= items).toBe(true)
})

law("the last page is never empty", domain<[Items, PerPage]>(), ([items, perPage]) => {
  expect((pageCount(items, perPage) - 1) * perPage < items).toBe(true)
})
```

Vitest runs the test and both laws together.

<p align="center">
  <img alt="A Vitest run: the unit test passes on its one input, the law &quot;every item is on a page&quot; is proved for 100,000,000 inputs, and the law &quot;the last page is never empty&quot; fails with the counterexample items = 1, perPage = 1" src="assets/vitest.svg" width="760">
</p>

The first law is proved. The second is false, and the run names an input that
breaks it: one item at one per page gives two pages. Change the body to
`Math.ceil(items / perPage)` and both laws are proved for all 100,000,000
combinations.

`pages.ts` is not annotated, rewritten or moved. Law files type-check, format
and refactor with the rest of the project.

## Quick start

```sh
npm install --save-dev @bytewaveco/pudding@beta typescript
```

Add law files to what Vitest collects.

```ts
// vitest.config.ts
import { defineConfig } from "vitest/config"

export default defineConfig({
  test: { include: ["**/*.test.ts", "**/*.law.ts"] },
})
```

Write a `*.law.ts` file next to the code and run `npx vitest`. Without Vitest
there is nothing to configure:

```sh
npx pudding                 # check every *.law.ts
npx pudding watch           # check again on every change
```

Pudding needs Node 24 and a TypeScript 7 compiler in your project. Lean 4.36
comes with `npm install` on macOS and Linux, arm64 and x64. Law files do not
have to be listed in a tsconfig, and a project without a tsconfig works.

<details>
<summary><b>Projects on an older TypeScript</b></summary>

Pudding reads your code with the compiler your project already has, so the
laws are checked against the same TypeScript as everything else. It is a peer
dependency, and either of these serves:

- `typescript` 7.0 or newer;
- [`tsrs`](https://github.com/oxc-project/tsrs), the Rust port of TypeScript 7.

When both are installed, `typescript` is used if it is version 7, and `tsrs`
otherwise. Set `PUDDING_COMPILER` to `typescript` or `tsrs` to choose. Each run
names the compiler it used in its last lines.

A project can keep an older `typescript` for its other tools and give Pudding
`tsrs`. Package managers then report that `typescript` is older than Pudding
asks for, and need to be told that this is intended. With npm, in
`package.json`:

```json
{ "overrides": { "@bytewaveco/pudding": { "typescript": "$typescript" } } }
```

With pnpm, in `pnpm-workspace.yaml`:

```yaml
peerDependencyRules:
  allowedVersions:
    '@bytewaveco/pudding>typescript': '6'
```

</details>

<details>
<summary><b>Where Lean comes from</b></summary>

Lean arrives as an optional dependency: a package of about 110 MB holding the
part of Lean that Pudding uses. Where it did not arrive, because optional
dependencies are switched off or the package manager skipped it, `pudding`
offers to download Lean the first time, and `npx pudding install-lean` does
the same without asking. That fetches the official Lean release, checks it
against a recorded SHA-256, and keeps the same part of it in a cache shared by
all your projects. To use a Lean you already have, set `PUDDING_LEAN` to the
binary; a Lean installed with elan is found on its own.

</details>

## Runs in Vitest

A law file is a Vitest test file. Each law is a test next to your unit tests,
and watch mode, `-t`, the UI and editor integrations work as they do for any
test. `describe`, `law.skip`, `law.only` and `law.todo` become their Vitest
counterparts.

A passing test means the law was proved. Where the code is outside what
Pudding can prove, the law is executed instead, and the test carries a note
saying so. Set `strict` in `pudding.config.ts` to fail those.

A failing test shows the counterexample and points at the `expect` that broke:

```
 FAIL  src/pages.law.ts > the last page is never empty
LawFailed: the expectation does not hold
  expect((pageCount(items, perPage) - 1) * perPage < items).toBe(true)
  with items = 1, perPage = 1
  actual:   false
  expected: true
 ❯ src/pages.law.ts:12:3
```

Each file is proved by its own Pudding run when its first law starts, so a
law file costs a few hundred milliseconds more under Vitest than under
`pudding`, which reads all of them in one go. Vitest is an optional peer
dependency, version 3 or newer.

## Checked by Lean 4

Pudding does not decide for itself whether a law holds. It turns each `expect`
into a theorem and gives it to Lean, a proof assistant whose kernel checks
every proof. This law

```ts
law("abs is never negative", domain<bigint>(), x => {
  expect(abs(x) >= 0n).toBe(true)
})
```

becomes this theorem about every integer:

```lean
theorem c0 (x0 : Int) : (decide ((0 : Int) ≤ (if (decide (x0 < (0 : Int))) then (-x0) else x0))) = true := by grind
```

You do not write Lean or read it. The theorems are generated, and
`pudding --emit laws.lean` writes them out when you want to look.

Laws over finite inputs, such as booleans, unions and bounded integers, are
decided by evaluating every case in the kernel, and never need help. Laws over
unbounded inputs, such as `bigint` and `string`, go to Lean's `grind`, which
handles linear arithmetic, case splits, and division and remainder by
constants. A theorem counts only when Lean reports no error for it and
confirms that it rests on nothing but Lean's standard axioms, so an unfinished
proof (`sorry`) is rejected.

### Supplying a proof

When `grind` is not enough, pass a Lean tactic script:

```ts
law("a product of positives is positive", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: "intro h; simp_all; exact Int.mul_pos h.1 h.2" })
```

You or an agent can work on a proof with ordinary Lean tooling, starting from
the emitted theorems. Nobody has to review the script: Lean rejects it if it
is wrong or unfinished. A script is a sequence of tactics and nothing else. It
is checked in a file of its own, and it may not contain comments, string
literals or unbalanced parentheses, so that it cannot go on to define
anything. The Lean that comes with `npm install` holds only the part of Lean's
library Pudding itself uses; a proof that names other lemmas needs
`pudding install-lean --full` or your own Lean.

## Writing laws

```ts
law(name, domain<T>(), input => { ... }, options?)
law(name, () => { ... }, options?)          // fixed values, no domain
law.skip(...)   law.only(...)   law.todo(name)
describe(name, () => { ... })               // also describe.skip, describe.only
```

`domain<T>()` describes the inputs by type.

| Type | Inputs covered |
|---|---|
| `boolean`, a union of string, bigint or number literals | every member |
| `bigint`, `string` | every value |
| `Integer` | every whole number a `number` holds exactly |
| `Integer<Min, Max>` | every whole number from `Min` to `Max` |
| an object type | every plain object with exactly its properties, in every combination of their values |
| a tuple | every combination of its elements |
| a union of object types | every alternative |

A plain `number` cannot be an input, because it also covers fractions, NaN and
infinities. Functions that take a `number` accept an `Integer`. An object type
with an index signature, such as `Record<string, boolean>`, cannot be an input
either, because its values cannot be listed.

A law's callback is an ordinary synchronous function, and a law file contains
only `law()` and `describe()` calls and declarations at its top level, so that
every law that would be registered is also read.

Inside a law you can declare values, loop, guard with `if`, leave early with
`return`, call helpers that assert, and assert with `expect(a).toEqual(b)`,
`expect(a).toBe(b)` and their `.not` forms.

## What it can prove

Pudding reads only the code a law reaches, and a module may contain anything
else. It proves laws about the plain data and arithmetic that business rules
are made of. The [examples](examples) cover money, orders, stock, ballots, job
queues and leave requests.

- **Proved:** booleans, bigints, strings and whole numbers; objects, arrays
  and tuples; `if`, `switch` and loops of known length; local changes in
  place; functions in any module; `const` tables; `Math` rounding; `.map`,
  `.reduce`, `.some`, `.every` and `.includes`.
- **Refused:** fractions, loops whose length depends on an input, recursion,
  classes, async code, regular expressions and library calls.

A refused law is not lost. Pudding executes it against the real code, on every
input of a finite domain or a sample of an unbounded one, and reports it as
*checked* or *sampled*, never as proved. It is promoted to *proved* when the
subset grows. [The supported subset](docs/supported-subset.md) lists every
construct, with the limits worth knowing.

## What a run reports

```
$ npx pudding --reporter verbose
 ✗ money.law.ts (3 laws)
   ✓ clamp stays within its bounds
   ✗ clamp is idempotent
      the expectation does not hold
      money.law.ts:12:3  expect(clamp(clamp(x, lo, hi), lo, hi)).toEqual(clamp(x, lo, hi))
      with x = 0n, lo = 0n, hi = -1n
      actual:   0n
      expected: -1n
   ~ cents survive a round trip  executed on sampled inputs, not proved
      note: not proved: calling `.split` on a string is not supported (money.ts:12:28)

  Laws    1 proved, 1 sampled only, 1 failed
  Proofs  3 theorems, 0 finite cases, Lean 4.36.0, TypeScript 7.0.2
  Time    546 ms
```

| State | Meaning |
|---|---|
| **proved** | Lean accepted a proof for every input. |
| **checked** | The code is outside the supported subset, so the law was executed against the real code for every input of a finite domain. |
| **sampled** | As above, but the domain is unbounded, so the law was executed on a sample. |
| **failed** | The law is false, proves nothing, or could not be verified at all. |
| **skipped**, **todo** | Marked that way, or filtered out. |

A failed law says why:

- **A counterexample.** The inputs are named as the law names them, with both sides of the failed equality.
- **A throw that can be reached**, including division by zero, a lookup with a key the table does not have, and a function that ends without returning. A law holds only if the code it calls cannot throw for the inputs it covers.
- **A law file that throws when it is loaded.** Nothing in it holds at run time, whatever was proved.
- **A number that stops being exact.** A result beyond 2^53 − 1, or a remainder by zero.
- **An expectation that is never reached.** A guard that is never true would otherwise pass silently. When Pudding can neither find an input that reaches an expectation nor prove that none exists, the law keeps its verdict and carries a note saying so.
- **No proof and no counterexample.** The law may be true but beyond the automation. [Supply a proof](#supplying-a-proof).
- **A disagreement between the model and the running code.** See [What a proof means](#what-a-proof-means).

`--strict` turns *checked* and *sampled* into failures, for CI on modules where
only a proof will do.

## Command line and configuration

```
pudding [filters...]        check law files whose path contains a filter
pudding watch [filters...]  check again whenever a file changes
pudding install-lean        download the Lean runtime
```

| Option | Effect |
|---|---|
| `-t, --name <pattern>` | only laws whose full name matches the regular expression |
| `-w, --watch` | same as the `watch` command |
| `--strict` | fail when a law was only executed, not proved |
| `--reporter <name>` | `default`, `verbose`, `json` or `github` |
| `--no-cache` | ignore results from earlier runs |
| `--no-cross-check` | do not execute laws against the real code |
| `--emit <file>` | also write the generated Lean source |
| `--cwd <dir>` | project directory |

The `github` reporter is chosen automatically inside GitHub Actions and
annotates the lines that failed. The same run is available from code as
`run()` in `@bytewaveco/pudding/runner`.

A `pudding.config.ts` is optional, and applies under Vitest too.

```ts
import { defineConfig } from "@bytewaveco/pudding"

export default defineConfig({
  include: ["src/**/*.law.ts"],        // default: **/*.law.ts
  exclude: ["src/legacy/**"],
  tsconfig: ".nuxt/tsconfig.app.json", // whose paths and options to read the laws with
  strict: false,                       // fail laws that were only executed
  crossCheck: true,                    // execute laws against the real code
  reporter: "default",
})
```

`tsconfig` matters when your imports use path aliases that the root
`tsconfig.json` does not define, as in a Nuxt project.

## How it works

<p align="center">
  <img alt="Your law file and your code go into Pudding. The TypeScript 7 compiler reads them, each law is translated into obligations, and Lean 4 proves them, while each law is also executed against the real code. When Lean accepts, the law holds for every input. When Lean rejects, Pudding reports a counterexample." src="assets/how-it-works.svg" width="760">
</p>

1. **Read.** The TypeScript 7 compiler API type-checks the law files and resolves every name and type. Type errors stop the run.
2. **Translate.** Each law is evaluated symbolically. Functions are inlined, objects, arrays and loops are resolved, and what remains is a set of obligations over booleans, integers and strings: one per `expect`, plus one per reachable `throw`, division, or number that could stop being exact.
3. **Prove.** Obligations over finite inputs become one Lean theorem each, decided by evaluating every case in the kernel. Obligations with unbounded inputs are handed to `grind`, with a slower fallback under the full library before a rejection is reported.
4. **Explain.** For a rejected obligation Pudding searches for a counterexample by evaluating the model in JavaScript.
5. **Cross-check.** In a worker thread, each law is executed against the real code and compared with the model.

Proved theorems are remembered by their full text and the Lean version, so
Lean is only asked about what changed. The TypeScript side is read afresh on
every run: reusing a whole result would mean guessing that nothing affecting
module resolution had changed.

All runs on the machine share one limit of a Lean process per core, so
Vitest proving several law files at once does not start a Lean per core for
each of them. Where the temporary directory cannot hold the limit, Lean runs
without it.

## What a proof means

A *proved* law is a theorem about a model of your code. These are the main
things that stand between that theorem and the code that runs.

- The translator is trusted, so every law is also executed against the real
  code and compared with the model. A disagreement fails the law.
- Inputs are plain data with exactly the properties their type declares.
- A `number` is modeled as the whole number it holds, and every result must be
  proved to stay within 2^53 − 1.
- Built-ins such as `Math` and array methods are modeled as the language
  defines them. If any file of the project assigns to one, no law is proved.

[What a proof means](docs/what-a-proof-means.md) lists everything that stands
between a theorem and the code that runs.

## Contributing

Pudding is in beta. [CONTRIBUTING.md](CONTRIBUTING.md) covers building,
testing, the fuzzer and releasing, and [AGENTS.md](AGENTS.md) is the short
version for coding agents.

[MIT](LICENSE)
