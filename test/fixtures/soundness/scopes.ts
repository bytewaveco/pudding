// More cases where the obvious reading of the code is not what JavaScript does.

const label = "open"
/** A closure made by a default cannot see what the function body declares, so it reads the module's `label`. */
export function defaultScope(id: bigint, read = () => label) {
  const label = "closed"
  return id === 12345n ? read() : "closed"
}

/** A `var` belongs to the whole function, so `flag` here is the inner one, which is undefined. */
export function varScope(n: bigint) {
  const flag = true
  function read() {
    if (false) { var flag: boolean | undefined = true }
    return flag
  }
  return n === 12345n ? read() : true
}

/** Inside a named function expression, its name means itself. */
export function ownName() {
  const lookup = (_: boolean) => false
  const run = function lookup(done: boolean): boolean {
    return done || lookup(true)
  }
  return run(false)
}

/** `map` checks that it was given a function even when the array is empty. */
export const emptyMap = () => ([] as bigint[]).map(1 as any)
