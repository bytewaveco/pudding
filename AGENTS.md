# AGENTS.md

Pudding proves laws about TypeScript functions. It reads `*.law.ts` files with
the project's TypeScript 7 compiler, translates each law into obligations, and
has Lean 4 check them. Laws also run as Vitest tests.

[README.md](README.md) is the user-facing overview.
[docs/supported-subset.md](docs/supported-subset.md) lists what can be proved,
and [docs/what-a-proof-means.md](docs/what-a-proof-means.md) what a proof
rests on. [CONTRIBUTING.md](CONTRIBUTING.md) has the file map, the fuzzer, the
Lean runtime packages and releasing. Read it before touching any of those.

## Checks

```sh
npm test                                # builds, then node --test test/*.test.ts
npm run proof                           # builds, then proves examples/
npm run typecheck
npm run fuzz -- --seed 3 --programs 300 # after any change to src/translate.ts or src/ir.ts
```

Tests and examples import `dist/`, so use these scripts, which build first.
After a change to how code is read (`src/compiler.ts`, `src/translate.ts`),
run `npm test` again with `PUDDING_COMPILER=tsrs`. Lean must be installed
(`npx pudding install-lean`).

## Easy to break

- A law reported as _proved_ that is false is the worst bug this project can
  have. When the translator cannot model a construct exactly as JavaScript
  runs it, throw `Unsupported` so the law falls back to being executed. Do not
  approximate.
- Fixture laws announce their expected status in their name: `FALSE:`,
  `VACUOUS:` and `UNPROVED:` must fail, `CHECKED` and `SAMPLED` must land
  there, and any other name must be proved (`announced()` in
  `test/pudding.test.ts`). A new fixture law follows this.
- The trimmed Lean runtime holds only the modules that the header in
  `src/lean.ts` imports. Changing those imports means new runtime packages
  (CONTRIBUTING.md, Releasing).
- `.lab/` and `test/fixtures/review-*/` are gitignored scratch. Tests must not
  depend on them.

## Conventions

- Commit messages are `type(scope): summary`, with the scope naming the area:
  `translate`, `lean`, `runner`, `cli`, `vitest`, `compiler`, `install`,
  `core`, `readme`, `package`.
- If a change contradicts a statement in the README or `docs/`, fix that
  statement in the same commit. A change to what can be proved updates
  `docs/supported-subset.md`.
- Output shown in the README is real output. Rerun the command before
  editing it.
