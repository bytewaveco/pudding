// Functions whose behaviour hinges on details of JavaScript that are easy to
// model wrongly. Each one misbehaves only at 424242n or with no input at all.

/** `result` is undefined, not unreachable, when the branch is not taken. */
export function unsetLet(n: bigint) {
  let result: boolean | undefined
  if (n !== 424242n) result = true
  return result
}

/** Passing undefined makes the default run, and the default can throw. */
export function defaultOnUndefined(n: bigint) {
  function empty() {}
  function validate() { if (n === 424242n) throw Error("invalid") }
  function use(value = validate()) { return true }
  return use(empty())
}

/** `value` is declared after the branch, so reading it from the else branch throws. */
export function readAcrossBranches(n: bigint) {
  function read() { return value }
  if (n !== 424242n) {
    if (n < 0n) return true
  } else { read() }
  const value = true
  return value
}

/** A shorthand property reads the binding too. */
export function shorthandRead(n: bigint) {
  function read() { return { value } }
  if (n === 424242n) read()
  const value = true
  return value
}

/** A number is never equal to a bigint. */
export function mixedIncludes(n: number | bigint) {
  const items: (number | bigint)[] = [424242]
  return items.includes(n)
}

export function mixedSwitch(n: number | bigint) {
  switch (n) {
    case 424242: return true
    default: return false
  }
}

/** This `expect` is the function's own, and it throws. */
export function ownExpect(n: bigint) {
  function expect(x: bigint) {
    if (x === 424242n) throw Error("invalid")
    return { toBe(y: bigint) {} }
  }
  expect(n).toBe(n)
  return true
}

/** The switch's own `pick` is in scope when the case label is evaluated. */
export function switchScope(pick: () => boolean) {
  switch (true) {
    case pick(): return true
    default:
      function pick() { return false }
      return false
  }
}

/** The loop's `item` already shadows the outer one while the iterable is evaluated: this throws. */
export function loopHeader() {
  const item = true
  function items(read: () => boolean): boolean[] { return [read()] }
  for (const item of items((): boolean => item)) {}
  return true
}

/** The second declarator's `flag` shadows the outer one while the first initializer runs: this throws. */
export function forInitializer() {
  const flag = true
  function read(get: () => boolean) { return get() }
  for (let first = read(() => flag), flag = false; first; ) break
  return true
}

/** The second parameter's `flag` shadows the outer one while the first default runs: this throws. */
export function parameterScope() {
  const flag = true
  function read(get: () => boolean) { return get() }
  function value(first = read(() => flag), flag = false) { return first }
  return value()
}
