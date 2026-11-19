# Pudding

Pudding proves laws about TypeScript functions you already have. You write a
law the way you would write a Vitest test, against the real implementation, and
Pudding proves it for **every** input instead of the ones you thought of. Lean 4
checks the proofs.

```ts
// orders.law.ts
import { domain, expect, law } from "pudding"
import { canMove, isTerminal, ship, type Order, type Status } from "./orders.ts"

law("a paid, placed order ships", domain<Order>(), order => {
  if (order.status !== "placed" || !order.paid) return
  expect(ship(order)).toEqual({ status: "shipped", paid: true })
})

law("nothing leaves a terminal status", domain<[Status, Status]>(), ([from, to]) => {
  if (isTerminal(from)) expect(canMove(from, to)).toBe(false)
})
```

The implementation is not annotated, rewritten or moved. Law files are ordinary
TypeScript: they type-check, format and refactor with the rest of the project.

## Getting started

Pudding needs Node 24, TypeScript 7 and Lean 4.36.

```sh
npm install
npx pudding install-lean   # downloads Lean 4.36.0 into .toolchain/
npm run proof              # builds, then checks every *.law.ts
npm test
```

`install-lean` keeps only the parts of the toolchain Pudding uses: about
570 MB on disk instead of 3 GB. Pass `--full` to keep everything. To use a Lean
you already have, set `PUDDING_LEAN` to the binary. The installer's download
step has not been exercised end to end; the pruning step has.

Law files must be included by the project's `tsconfig.json`.

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
      note: not proved: only strings can be interpolated, but this is a bigint (money.ts:38:37)
```

Each law ends in one of four states.

| State | Meaning |
|---|---|
| **proved** | Lean accepted a proof for every input. |
| **checked** | The code is outside the supported subset, so the law was executed against the real code for every input of a finite domain. |
| **sampled** | As above, but the domain is unbounded, so the law was executed on a sample. |
| **failed** | The law is false, proves nothing, or could not be verified at all. |

A failed law says why:

- **A counterexample.** The inputs are named as the law names them, with both sides of the failed equality.
- **A throw or a division by zero that can be reached.** A law holds only if the code it calls cannot throw for the inputs it covers.
- **An expectation that is never reached.** A guard that is never true would otherwise pass silently.
- **No proof and no counterexample.** The law may be true but beyond the automation. Supply a proof (see below).
- **A disagreement between the model and the running code.** See "What a proof means".

`--strict` turns *checked* and *sampled* into failures, for CI on modules where
only a proof will do.

## Writing laws

```ts
law(name, domain<T>(), input => { ... }, options?)
law(name, () => { ... }, options?)          // fixed values, no domain
```

`domain<T>()` describes the inputs by type.

| Type | Inputs covered |
|---|---|
| `boolean`, a union of string or bigint literals | every member |
| `bigint`, `string` | every value |
| an object type | every combination of its properties |
| a tuple | every combination of its elements |
| a union of object types | every alternative |

Inside the callback you can declare `const` values, guard with `if`, leave early
with `return`, and assert with `expect(a).toEqual(b)`, `expect(a).toBe(b)` and
their `.not` forms.

### Supplying a proof

Laws over finite inputs are decided by evaluation and never need help. Laws
over `bigint` and `string` use Lean's `grind`, which handles linear arithmetic,
case splits, and division and remainder by constants. When that is not enough,
pass a Lean tactic script:

```ts
law("a product of positives is positive", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: "intro h; simp_all; exact Int.mul_pos h.1 h.2" })
```

`pudding --emit laws.lean` writes the theorems, so you or an agent can work on
a proof with ordinary Lean tooling. Nobody has to review the script: Lean
rejects it if it is wrong.

## The supported subset

Pudding reads only the code a law reaches. A module may contain anything else.

- **Values:** `boolean`, `bigint`, `string`, object literals, array literals and tuples, arrow functions.
- **Operators:** `===` `!==` `&&` `||` `!` `?:`, bigint `+ - * / % < <= > >=`, string `+` and template literals.
- **Statements in functions:** `const`, `if`/`else`, `switch`, `return`, `throw`, nested functions.
- **Functions:** declarations and arrows, in any module of the project, with defaults and destructured parameters.
- **Data:** module-level `const` tables, indexed by a key whose type guarantees it is present; `.includes`, `.some`, `.every` and `.map` on arrays of known length.

Not supported: `number` (it is floating point; use `bigint` for quantities),
`let` and loops, recursion, classes, async code, regular expressions, and
library calls. Pudding refuses these at the exact expression and falls back to
executing the law, so a law can always be written and gets promoted to
*proved* when the subset grows.

## What a proof means

A *proved* law is a theorem about a model of your code. Four things stand
between the theorem and the code that runs.

1. **The translation.** Pudding's translator and its constant folding are trusted. To catch mistakes, every law is also executed against the real code and compared with the model on all inputs of a small finite domain or a sample of a large one. A disagreement fails the law.
2. **Module data.** A table such as `const transitions = {...}` is assumed to keep its initial value. Pudding refuses a table that is assigned to or mutated by name in its module, or whose module runs statements on load. It does not follow other names for the same object.
3. **Strings.** `string` inputs range over well-formed Unicode text. JavaScript strings with unpaired surrogates are not covered.
4. **Lean.** Finite laws are checked by Lean's kernel. Other proofs are found by tactics and checked by the kernel.

## Configuration

```ts
// pudding.config.ts
import { defineConfig } from "pudding"

export default defineConfig({
  include: ["src/**/*.law.ts"],   // default: **/*.law.ts
  strict: false,                  // fail laws that were only executed
  crossCheck: true,               // execute laws against the real code
})
```

| CLI option | Effect |
|---|---|
| `--strict` | fail when a law was only executed, not proved |
| `--no-cache` | ignore earlier results |
| `--no-cross-check` | do not execute laws against the real code |
| `--emit <file>` | also write the generated Lean source |
| `--json` | print the report as JSON |
| `--verbose` | list every law |
| `--cwd <dir>` | project directory |

The same run is available from code as `run()` in `pudding/runner`.

## How it works

1. **Read.** The TypeScript 7 compiler API type-checks the law files and resolves every name and type. Type errors stop the run.
2. **Translate.** Each law is evaluated symbolically. Functions are inlined, objects and arrays are resolved, and what remains is a set of obligations over booleans, integers and strings: one per `expect`, plus one per reachable `throw` or division.
3. **Prove.** Obligations over finite inputs become one Lean theorem each, decided by evaluating every case in the kernel. Obligations with unbounded inputs are specialized over their finite inputs and handed to `grind`, with a slower fallback under the full library before a rejection is reported.
4. **Explain.** For a rejected obligation Pudding searches for a counterexample by evaluating the model in JavaScript.
5. **Cross-check.** Each law is executed against the real code and compared with the model.

Proved theorems are cached by their text and the Lean version, and a run over
an unchanged project reuses the previous report. On an Apple M-series laptop
the 20 example laws take about 0.4 s from scratch, under 0.1 s when only
unrelated code changed, and about 60 ms when nothing changed.

## Repository layout

- [src/translate.ts](src/translate.ts): TypeScript to obligations.
- [src/ir.ts](src/ir.ts): the expression language, its simplifier and its evaluator.
- [src/lean.ts](src/lean.ts): obligations to Lean theorems, and running Lean.
- [src/runner.ts](src/runner.ts): the run, caching, counterexamples and the cross-check.
- [examples/](examples): laws that pass.
- [test/fixtures/suite/](test/fixtures/suite): laws that are meant to fail, be vacuous, or fall back, with the tests that pin each outcome.

## Limits worth knowing

- The TypeScript API Pudding uses is published under `typescript/unstable`, so the TypeScript version is pinned.
- Symbolic strings support equality and concatenation only, and proofs about them rarely go beyond what simplification settles.
- Products of two unknowns are outside `grind`'s arithmetic; such laws need a supplied proof.
- Each obligation is printed as a tree, so deeply nested calls of functions that use an argument several times grow quickly. Pudding refuses terms past a size limit.
- There is no watch mode, and the prebuilt Lean download covers macOS and Linux only.
