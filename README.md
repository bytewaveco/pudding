# Pudding

Pudding proves laws about TypeScript functions you already have. You write a
law the way you would write a Vitest test, against the real implementation, and
Pudding proves it for **every** input instead of the ones you thought of. Lean 4
checks the proofs.

```ts
// cart.law.ts
import { describe, domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { subtotal, pageCount, type Item } from "./cart"

describe("cart", () => {
  law("adding an item adds its cost", domain<[Item, Item]>(), ([first, second]) => {
    expect(subtotal([first, second])).toEqual(subtotal([first]) + second.price * second.quantity)
  })

  law("pages cover every item", domain<[Integer<0, 1000000>, Integer<1, 50>]>(), ([items, perPage]) => {
    expect(pageCount(items, perPage) * perPage >= items).toBe(true)
  })
})
```

The implementation is not annotated, rewritten or moved. Law files are ordinary
TypeScript: they type-check, format and refactor with the rest of the project.

## Getting started

Pudding needs Node 24. It brings its own TypeScript 7 for reading your code,
and it needs Lean 4.36 for the proofs.

```sh
npm install --save-dev @bytewaveco/pudding@beta
npx pudding                 # check every *.law.ts
npx pudding watch           # check again on every change
```

There is nothing to configure. Law files do not have to be listed in a
tsconfig, and a project without a tsconfig works.

On macOS and Linux, arm64 and x64, Lean arrives with `npm install` as an
optional dependency: a package of about 110 MB holding the part of Lean that
Pudding uses. Where it did not arrive, because optional dependencies are
switched off or the package manager skipped it, `pudding` offers to download
Lean the first time, and `npx pudding install-lean` does the same without
asking. That fetches the official Lean release, checks it against a recorded
SHA-256, and keeps the same part of it in a cache shared by all your projects.
To use a Lean you already have, set `PUDDING_LEAN` to the binary; a Lean
installed with elan is found on its own.

## The command line

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

## Running under Vitest

A law file is also a Vitest test file. Add the pattern to the files Vitest
collects, and every law shows up as a test next to your unit tests:

```ts
// vitest.config.ts
import { defineConfig } from "vitest/config"

export default defineConfig({
  test: { include: ["**/*.test.ts", "**/*.law.ts"] },
})
```

```
 ✓ src/cart.test.ts (1 test)
 ❯ src/cart.law.ts (2 tests | 1 failed)
   ✓ the order of two items does not matter
   × FALSE: quantity is ignored

 FAIL  src/cart.law.ts > FALSE: quantity is ignored
LawFailed: the expectation does not hold
  expect(subtotal([item])).toEqual(item.price)
  with item.price = 1n, item.quantity = 0n
  actual:   0n
  expected: 1n
 ❯ src/cart.law.ts:8:3
```

A passing test means what it means on the command line: the law was proved,
or executed when it could not be, and a law that was only executed carries a
note saying so. `describe`, `law.skip`, `law.only` and `law.todo` become
their Vitest counterparts, and `pudding.config.ts` still applies, so `strict`
turns executed-only laws into failures here too. Watch mode, `-t`, the UI and
editor integrations work as they do for any test.

Each file is proved by its own Pudding run when its first law starts, so a
law file costs a few hundred milliseconds more under Vitest than under
`pudding`, which reads all of them in one go. Vitest is an optional peer
dependency, version 3 or newer.

## Configuration

A `pudding.config.ts` is optional.

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

Inside a law you can use anything from the supported subset below: declare
values, loop, guard with `if`, leave early with `return`, call helpers that
assert, and assert with `expect(a).toEqual(b)`, `expect(a).toBe(b)` and their
`.not` forms.

### Supplying a proof

Laws over finite inputs are decided by evaluation and never need help. Laws
over unbounded inputs use Lean's `grind`, which handles linear arithmetic,
case splits, and division and remainder by constants. When that is not enough,
pass a Lean tactic script:

```ts
law("a product of positives is positive", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: "intro h; simp_all; exact Int.mul_pos h.1 h.2" })
```

`pudding --emit laws.lean` writes the theorems, so you or an agent can work on
a proof with ordinary Lean tooling. Nobody has to review the script: Lean
rejects it if it is wrong or unfinished. A script is a sequence of tactics and
nothing else. It is checked in a file of its own, and it may not contain
comments, string literals or unbalanced parentheses, so that it cannot go on
to define anything. The trimmed Lean that `install-lean` leaves holds
only the part of Lean's library Pudding itself uses; a proof that names other
lemmas needs `pudding install-lean --full` or your own Lean.

## What a run reports

```
 ✗ money.law.ts (3 laws)
   ✓ clamp stays within its bounds
   ✗ clamp is idempotent
      the expectation does not hold
      money.law.ts:12:3  expect(clamp(clamp(x, lo, hi), lo, hi)).toEqual(clamp(x, lo, hi))
      with x = 0n, lo = 0n, hi = -1n
      actual:   0n
      expected: -1n
   ~ cents survive a round trip  executed on sampled inputs, not proved
      note: not proved: calling `.padStart` on a string is not supported (money.ts:38:56)
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
- **No proof and no counterexample.** The law may be true but beyond the automation. Supply a proof.
- **A disagreement between the model and the running code.** See "What a proof means".

`--strict` turns *checked* and *sampled* into failures, for CI on modules where
only a proof will do.

## The supported subset

Pudding reads only the code a law reaches. A module may contain anything else.

- **Values:** `boolean`, `bigint`, `string`, whole `number`s, `undefined`, object literals, array literals and tuples, functions.
- **Operators:** `===` `!==` `&&` `||` `!` `?:`; `+ - * % < <= > >=` on bigint and number; `/` on bigint; string `+` and template literals.
- **Statements:** `const` and `let`, assignment and `+=`-style updates of local variables, `if`/`else`, `switch`, `for…of` over an array of known length, `for`, `while` and `do` loops whose condition is settled at each round, `break`, `continue`, `return`, `throw`.
- **Functions:** declarations and arrows, in any module of the project, with defaults and destructured parameters.
- **Data:** module-level `const` tables, indexed by a key whose type guarantees it is present; `.includes`, `.some`, `.every`, `.map`, `.reduce` and `.length` on arrays of known length.
- **Numbers:** `Math.floor`, `ceil` and `trunc` of a quotient or a value, `Math.abs`, `sign`, `min`, `max`, and `String`, `Number` and `BigInt` conversions.

Refused, with the reason, at the exact expression:

- fractions, plain `number` division and `Math.round` of a quotient;
- changing an object or array in place, because two names can refer to the same object;
- a function that uses a variable which is reassigned outside it;
- reading a `const` or `let` before its declaration has run, and `__proto__`;
- an import such as `./x.js` when both `x.js` and `x.ts` exist, because TypeScript reads one and Node runs the other;
- `var`, loops whose length depends on an input, recursion, classes, async code, regular expressions and library calls.

A refused law is executed instead and reported as *checked* or *sampled*, so a
law can always be written and gets promoted to *proved* when the subset grows.

## What a proof means

A *proved* law is a theorem about a model of your code. These things stand
between the theorem and the code that runs.

1. **The translation.** Pudding's translator and its constant folding are trusted. To catch mistakes, every law is also executed against the real code and compared with the model, on all inputs of a small finite domain or a sample of a large one that includes the constants the law mentions. A disagreement fails the law. If the law file cannot be executed, the run says so in a warning. With `--no-cross-check` none of this happens, including noticing that a module throws when it loads.
2. **Inputs are plain data.** An object input has exactly the properties its type declares, held as ordinary values. TypeScript would also accept an object with extra properties, or one whose properties are getters; those are not covered.
3. **Module data.** A table such as `const transitions = {...}` is assumed to hold its initial value when a law runs. Anywhere in its module, a table may only be read in ways known to change nothing; anything else, such as passing it to a function, calling a method it defines, or giving it another name, makes Pudding refuse it. Two things are taken on trust: an installed package given a table declared `as const` does not change it, and no other module changes an exported table.
4. **Built-ins.** `Math`, `String`, array methods, iteration and the like are modeled as the language defines them. If any file of the project assigns to a built-in, no law is proved; they are executed instead. Pudding does not look inside installed packages.
5. **The files that run are the files TypeScript read.** Laws are executed against the files TypeScript resolved each import to. Where Node on its own would load a different file, as with some conditional `imports` and `exports`, the run says so in a warning.
6. **Numbers.** A `number` is modeled as the whole number it holds, and every result must be proved to stay within 2^53 − 1, where that model is exact. Zero and negative zero are one value, as `===` treats them.
7. **Strings.** `string` inputs range over well-formed Unicode text. JavaScript strings with unpaired surrogates are not covered.
8. **Lean.** Finite laws are checked by Lean's kernel. Other proofs are found by tactics and checked by the kernel. A theorem counts only when Lean reports no error for it and confirms that it rests on nothing but Lean's standard axioms, so an unfinished proof (`sorry`) is rejected.

## How it works

1. **Read.** The TypeScript 7 compiler API type-checks the law files and resolves every name and type. Type errors stop the run.
2. **Translate.** Each law is evaluated symbolically. Functions are inlined, objects, arrays and loops are resolved, and what remains is a set of obligations over booleans, integers and strings: one per `expect`, plus one per reachable `throw`, division, or number that could stop being exact.
3. **Prove.** Obligations over finite inputs become one Lean theorem each, decided by evaluating every case in the kernel. Obligations with unbounded inputs are handed to `grind`, with a slower fallback under the full library before a rejection is reported.
4. **Explain.** For a rejected obligation Pudding searches for a counterexample by evaluating the model in JavaScript.
5. **Cross-check.** In a worker thread, each law is executed against the real code and compared with the model.

Proved theorems are remembered by their full text and the Lean version, so
Lean is only asked about what changed. The TypeScript side is read afresh on
every run: reusing a whole result would mean guessing that nothing affecting
module resolution had changed.

## Developing

```sh
npm install
npx pudding install-lean
npm test          # builds, then runs the tests
npm run proof     # builds, then checks the examples
npm run fuzz -- --seed 3 --programs 2000
```

`npm run fuzz` is a differential fuzzer. It generates random functions inside
the supported subset, runs each in Node on every input of a small finite
domain, and checks that Pudding proves the law stating exactly those results
and never proves the same law with one result changed. It leans on the
scoping, hoisting and `undefined` rules that are easiest to model wrongly.

With `--unbounded` the inputs are all bigints or a wide range of whole
numbers, which Pudding proves with tactics. No table of results exists there,
so each function is compared with a copy that has one constant or operator
changed; when Node finds an input on which the two differ, the law that they
are equal must not be proved. Programs that expose a problem are kept under
`.lab/fuzz/failures/`.

- [src/translate.ts](src/translate.ts): TypeScript to obligations.
- [src/ir.ts](src/ir.ts): the expression language, its simplifier and its evaluator.
- [src/lean.ts](src/lean.ts): obligations to Lean theorems, and running Lean.
- [src/runner.ts](src/runner.ts): the run, caching and explaining failures.
- [src/crosscheck.ts](src/crosscheck.ts): executing laws against the real code.
- [scripts/pack-runtime.mjs](scripts/pack-runtime.mjs): builds the trimmed Lean runtime for a platform.
- [scripts/fuzz.mjs](scripts/fuzz.mjs): the differential fuzzer.
- [examples/](examples): laws that pass.
- [test/fixtures/](test/fixtures): laws that are meant to fail, be vacuous, or fall back, with the tests that pin each outcome.

### Shipping Lean as a package

Pudding looks for a package named `<its own name>-lean-<platform>-<arch>`,
so Lean is an ordinary optional dependency instead of a separate download.
Only `PUDDING_LEAN`, the `lean` setting and a whole Lean from
`install-lean --full` go before it. `scripts/pack-runtime.mjs` builds that package from an
official toolchain: the `lean` binary, its stripped shared libraries and the
264 compiled modules the generated theorems import.

```sh
npx pudding install-lean --full --local
npm run pack:runtime -- .toolchain/lean-4.36.0-darwin_aarch64 runtime --package
```

For macOS arm64 the result is 359 MB on disk and 108 MB as the `.tar.gz` npm
uploads. It gives the same verdicts as the full toolchain on the tests, the
examples and a benchmark of 4,661 generated theorems. The package is versioned
after Lean: Lean 4.36.0 gives 4.36.0, and `--build 1` gives 4.36.1 when the
set of modules changes under the same Lean.

### Releasing

Two workflows in `.github/workflows` do the work. `ci.yml` runs the tests, the
examples, the package smoke test and a short fuzzing run on Linux and macOS,
arm64 and x64. `release.yml` is started by hand and publishes one of two
things.

1. **The runtime packages**, only when Lean or the imports in `src/lean.ts`
   change. Run Release with target `runtime`. Each platform builds its own
   package, runs the tests against it and publishes it. Then pin the new
   version here and commit:

   ```sh
   npm install --save-optional --save-exact \
     @bytewaveco/pudding-lean-darwin-arm64@4.36.0 @bytewaveco/pudding-lean-darwin-x64@4.36.0 \
     @bytewaveco/pudding-lean-linux-arm64@4.36.0 @bytewaveco/pudding-lean-linux-x64@4.36.0
   ```

2. **Pudding itself.** Set the version in `package.json`, commit, and run
   Release with target `package`. It is published under the dist-tag in
   `publishConfig`, which is `beta` for now.

Both need an `NPM_TOKEN` secret that may publish to the `@bytewaveco` scope.
Tick `dry-run` to go through everything except the upload.

## Limits worth knowing

- The TypeScript API Pudding uses is published under `typescript/unstable`, so the TypeScript version is pinned.
- Division by an unknown and products of two unknowns are outside `grind`'s arithmetic. Bound the divisor with a small `Integer<Min, Max>`, which is checked value by value, or supply a proof.
- Symbolic strings support equality and concatenation only.
- Each obligation is printed as a tree, so deeply nested calls of functions that use an argument several times grow quickly. Pudding refuses terms past a size limit.
- Prebuilt Lean downloads exist for macOS and Linux only.
