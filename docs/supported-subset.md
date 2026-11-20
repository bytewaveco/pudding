# The supported subset

Pudding reads only the code a law reaches. A module may contain anything else.

A law over code outside the subset is refused, with the reason, at the exact
expression. A refused law is executed instead and reported as *checked* or
*sampled*, so a law can always be written and gets promoted to *proved* when
the subset grows.

## What can be proved

- **Values:** `boolean`, `bigint`, `string`, whole `number`s, `undefined`, object literals, array literals and tuples, functions.
- **Operators:** `===` `!==` `&&` `||` `!` `?:`; `+ - * % < <= > >=` on bigint and number; `/` on bigint; string `+` and template literals.
- **Statements:** `const` and `let`, assignment and `+=`-style updates of local variables, of properties and of array positions, `if`/`else`, `switch`, `for…of` over an array of known length, `for`, `while` and `do` loops whose condition is settled at each round, `break`, `continue`, `return`, `throw`.
- **Functions:** declarations and arrows, in any module of the project, with defaults and destructured parameters.
- **Data:** module-level `const` tables, indexed by a key whose type guarantees it is present; `.includes`, `.some`, `.every`, `.map`, `.reduce`, `.push` and `.length` on arrays of known length.
- **Changes in place:** `total.sum += x`, `list[0] = x` and `list.push(x)` on an object or array that the code under the law created itself. Two names for one object see each other's changes, a function changes what it is given, and a change behind a condition or an early return happens only on that path, all as in JavaScript.
- **Numbers:** `Math.floor`, `ceil` and `trunc` of a quotient or a value, `Math.abs`, `sign`, `min`, `max`, and `String`, `Number` and `BigInt` conversions.
- **Text:** `.padStart` and `.padEnd` to a known length, on a string known where it is used or on the text of a whole number, as in `String(cents % 100n).padStart(2, "0")`.

## What is refused

- fractions, plain `number` division and `Math.round` of a quotient;
- changing in place an object the code did not just create: one of the law's inputs, a module constant, something a `describe` shares between its laws, or the result of a condition choosing between two objects. Copy it first, as in `{ ...value }`;
- a change in place where JavaScript may skip it but a model must decide: on the right of `&&` or `||`, in a callback of `.some` or `.every`, and a `.push` on only one side of a condition;
- adding a property to an object, and array methods that reorder or shrink, such as `.sort` and `.pop`;
- a function that uses a variable which is reassigned outside it;
- reading a `const` or `let` before its declaration has run, and `__proto__`;
- an import such as `./x.js` when both `x.js` and `x.ts` exist, because TypeScript reads one and Node runs the other;
- `var`, loops whose length depends on an input, recursion, classes, async code, regular expressions and library calls.

## Limits worth knowing

- The compiler API Pudding uses is new in TypeScript 7 and changed between 7.0 and 7.1. Pudding is tested with `typescript` 7.0 and 7.1 and with `tsrs`; a later release may need a newer Pudding.
- Division by an unknown and products of two unknowns are outside `grind`'s arithmetic. Bound the divisor with a small `Integer<Min, Max>`, which is checked value by value, or [supply a proof](../README.md#supplying-a-proof).
- Symbolic strings support equality and concatenation only. Laws that need more, such as case analysis on a formatted number, are best stated over a small `Integer<Min, Max>`, where every value is checked.
- Each obligation is printed as a tree, so deeply nested calls of functions that use an argument several times grow quickly. Pudding refuses terms past a size limit.
- Where a law is checked value by value, a string may grow to 500 characters. Past that Lean's kernel gives up, so the law is executed instead and reported as not proved.
- Prebuilt Lean downloads exist for macOS and Linux only.
