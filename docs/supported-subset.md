# The supported subset

Pudding reads only the code a law reaches. A module may contain anything else.

A law over code outside the subset is refused, with the reason, at the exact
expression. A refused law is executed instead and reported as *checked* or
*sampled*, so a law can always be written and gets promoted to *proved* when
the subset grows.

## What can be proved

- **Values:** `boolean`, `bigint`, `string`, whole `number`s, `undefined`, object literals, array literals and tuples, functions, `Map` and `Set`.
- **Operators:** `===` `!==` `!` `?:`; `&&`, `||` and `??`, which give one of their two sides as JavaScript does; `?.`; `+ - * % < <= > >=` on bigint and number; `/` on bigint; string `+` and template literals.
- **Conditions:** any value, as JavaScript takes it: `false`, zero, the empty string and `undefined` are false, and every object, array and function is true.
- **Undefined:** a property that an object does not have, a position outside an array and a parameter the call leaves out all read as `undefined`. A lookup by a key that is not known where it is used gives `undefined` for a miss when its type allows that, as for `Record<string, T | undefined>`; where the type says the key is always there, a miss must be proved impossible. Reading a property of `undefined`, or calling it, is a throw, and like any throw it must be proved unreachable.
- **Statements:** `const` and `let`, destructuring with defaults and rest patterns, assignment and `+=`-style updates of local variables, of properties and of array positions, `if`/`else`, `switch`, `for…of` over an array of known length, a `Map` or a `Set`, `for`, `while` and `do` loops whose condition is settled at each round, `break`, `continue`, `return`, `throw`.
- **Functions:** declarations and arrows, in any module of the project, with defaults and destructured parameters. A function may read and assign a variable of a function that encloses it, while that function is still running: a callback of `.map` can keep a running total.
- **Data:** module-level `const` tables, indexed by a key whose type guarantees it is present; `.includes`, `.some`, `.every`, `.find`, `.map`, `.filter`, `.flatMap`, `.reduce`, `.at`, `.slice`, `.push` and `.length` on arrays of known length; `.sort` and `.toSorted` with a comparing function; `Array.from` of a list, a `Map`, a `Set` or `{ length }`.
- **Maps and Sets:** `new Map` and `new Set`, empty or from a list, with booleans, numbers, bigints and strings as keys; `.get`, `.set`, `.add`, `.has` and `.size`; looping over one and spreading it.
- **Changes in place:** `total.sum += x`, `list[0] = x`, `list.push(x)` and `list.sort(compare)` on an object or array that the code under the law created itself. Two names for one object see each other's changes, a function changes what it is given, and a change behind a condition or an early return happens only on that path, all as in JavaScript.
- **Numbers:** `Math.floor`, `ceil`, `trunc` and `round` of a quotient or a value, `Math.abs`, `sign`, `min`, `max`, and `String`, `Number` and `BigInt` conversions. `Infinity` and `-Infinity` where they are compared with a number, as in `end ?? Infinity`.
- **Text:** `.padStart` and `.padEnd` to a known length, on a string known where it is used or on the text of a whole number, as in `String(cents % 100n).padStart(2, "0")`.

## What is refused

- fractions and plain `number` division;
- changing in place an object the code did not just create: one of the law's inputs, a module constant, something a `describe` shares between its laws, or the result of a condition choosing between two objects. Copy it first, as in `{ ...value }`;
- a change in place, or an assignment to a variable outside a callback, where JavaScript may skip it but a model must decide: on the right of `&&`, `||` or `??`, in a callback of `.some`, `.every`, `.find` or `.sort`, and a `.push`, `.set` or `.add` on only one side of a condition;
- adding a property to an object, and array methods that shrink, such as `.pop`;
- sorting where the order depends on an input that has many values, a comparing function that does not order the elements consistently, and `.sort` without one;
- a function that uses a reassigned variable after the function that declared the variable has returned, such as a counter handed back by the function that made it;
- a function that uses the variable of a `for (let i = …)` loop around it, because JavaScript gives each round its own copy. Copy it into a `const` inside the loop;
- adding to a `Map` or a `Set` inside a loop over it, and a default in an array pattern that changes the list being taken apart;
- a property that every object inherits, such as `toString` read as a value, and objects as keys of a `Map` or a `Set`;
- reading a `const` or `let` before its declaration has run, and `__proto__`;
- an import such as `./x.js` when both `x.js` and `x.ts` exist, because TypeScript reads one and Node runs the other;
- `var`, loops whose length depends on an input, recursion, classes, async code, regular expressions and library calls.

## Limits worth knowing

- `Math.round` of a quotient is exact while the number divided stays strictly between -2^52 and 2^52, which each use must prove like any other bound.
- `.sort` and `.toSorted` take up to 64 elements, because every three of them are checked against each other.
- Law inputs are listed from their types, which needs `strictNullChecks`: without it a type does not say whether it holds `undefined`, and a law with a domain is executed instead of proved.
- Each element of a `.filter` that may or may not pass, and each result of a `.flatMap` that depends on a condition, doubles the lists there could be. Up to 8 such elements are followed.
- Each optional property of an input, and each part of it that may be `undefined`, multiplies the shapes the input can take. More than 64 shapes are refused, and so is an input type that refers to itself or has more than 10,000 parts.
- Looping over a `Map` or a `Set` needs to know which of its keys are equal. Keys that are inputs are fine for `.get`, `.has` and `.size`.
- The compiler API Pudding uses is new in TypeScript 7 and changed between 7.0 and 7.1. Pudding is tested with `typescript` 7.0 and 7.1 and with `tsrs`; a later release may need a newer Pudding.
- Division by an unknown and products of two unknowns are outside `grind`'s arithmetic. Bound the divisor with a small `Integer<Min, Max>`, which is checked value by value, or [supply a proof](../README.md#supplying-a-proof).
- Symbolic strings support equality and concatenation only. Laws that need more, such as case analysis on a formatted number, are best stated over a small `Integer<Min, Max>`, where every value is checked.
- Each obligation is printed as a tree, so deeply nested calls of functions that use an argument several times grow quickly. Pudding refuses terms past a size limit.
- Where a law is checked value by value, a string may grow to 500 characters. Past that Lean's kernel gives up, so the law is executed instead and reported as not proved.
- Prebuilt Lean downloads exist for macOS and Linux only.
