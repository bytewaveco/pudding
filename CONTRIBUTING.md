# Contributing

[README.md](README.md) describes Pudding from the outside. This file covers
working on it: building and testing, the fuzzer, the Lean runtime packages and
releasing.

## Developing

Pudding needs Node 24.

```sh
npm install
npx pudding install-lean
npm test          # builds, then runs the tests
npm run proof     # builds, then checks the examples
npm run fuzz -- --seed 3 --programs 2000
```

The tests and the examples import the build in `dist/`, so run them through
these scripts, which build first.

CI (`.github/workflows/ci.yml`) runs the type check, the tests, the examples,
the package smoke test (`npm run test:package`) and a short fuzzing run on
Linux and macOS, arm64 and x64. It then runs the tests and the fuzzer again
with `PUDDING_COMPILER=tsrs`, so that both compilers read the code.

Commit messages follow `type(scope): summary`, as in
`fix(lean): refuse strings too long for Lean's kernel to compare`.

## Where things are

- [src/compiler.ts](src/compiler.ts): finds the project's TypeScript 7 compiler.
- [src/translate.ts](src/translate.ts): TypeScript to obligations.
- [src/ir.ts](src/ir.ts): the expression language, its simplifier and its evaluator.
- [src/lean.ts](src/lean.ts): obligations to Lean theorems, and running Lean.
- [src/runner.ts](src/runner.ts): the run, caching and explaining failures.
- [src/crosscheck.ts](src/crosscheck.ts): executing laws against the real code.
- [src/vitest.ts](src/vitest.ts): the bridge that turns each law into a Vitest test.
- [scripts/pack-runtime.mjs](scripts/pack-runtime.mjs): builds the trimmed Lean runtime for a platform.
- [scripts/fuzz.mjs](scripts/fuzz.mjs): the differential fuzzer.
- [examples/](examples): laws that pass, over small modules of the kind business code is made of: money, orders, stock, leave requests.
- [test/fixtures/](test/fixtures): laws that are meant to fail, be vacuous, or fall back, with the tests that pin each outcome.

## The fuzzer

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

## Shipping Lean as a package

Pudding looks for a package named `<its own name>-lean-<platform>-<arch>`,
so Lean is an ordinary optional dependency instead of a separate download.
Only `PUDDING_LEAN`, the `lean` setting and a whole Lean from
`install-lean --full` go before it. `scripts/pack-runtime.mjs` builds that
package from an official toolchain: the `lean` binary, its stripped shared
libraries and the 264 compiled modules the generated theorems import.

```sh
npx pudding install-lean --full --local
npm run pack:runtime -- .toolchain/lean-4.36.0-darwin_aarch64 runtime --package
```

The result is about 360 MB on disk and 108 to 116 MB as the `.tar.gz` npm
uploads, depending on the platform. On macOS arm64 it gives the same verdicts
as the full toolchain on the tests, the examples and a benchmark of 4,661
generated theorems. The release workflow builds each platform's package on
that platform and runs the tests and the examples against it before
publishing. The package is versioned after Lean: Lean 4.36.0 gives 4.36.0, and
`--build 1` gives 4.36.1 when the set of modules changes under the same Lean.

## Releasing

`release.yml` in `.github/workflows` is started by hand and publishes one of
two things.

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
   `publishConfig`, which is `beta` for now, and `latest` is moved to it as
   well while every release is a beta.

Both need an `NPM_TOKEN` secret that may publish to the `@bytewaveco` scope.
Tick `dry-run` to go through everything except the upload.
