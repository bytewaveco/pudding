// Each function here behaves differently from what a naive reading suggests.

/** The inner declaration is hoisted to the top of its block, so it is the one called. */
export function hoisted() {
  function pick() { return true }
  {
    return pick()
    function pick() { return false }
  }
}

/** `read` sees the inner `value`, which is not initialized yet when it is called: this throws. */
export function deadZone() {
  const value = true
  {
    const read = () => value
    const result = read()
    const value = false
    return result
  }
}

/** TypeScript's `this` parameter does not exist at run time, so `true` is `value`. */
export function erasedThis(this: void, value = false) { return value }

/** The callback is passed an index, so its default is never used. */
export const callbackIndex = () => [true].some((_, index: number | false = false) => index === false)

/** The cast claims the key is always "ready"; it is whatever was passed. */
export const castKey = (key: string) => ({ ready: true })[key as "ready"]

/** In an object literal, `__proto__` sets the prototype instead of storing a property. */
export const protoLiteral = () => ({ __proto__: "metadata" }).__proto__

const flags = { ready: false }
export const configured = Object.assign(flags, { ready: true })
/** The table was changed while the module loaded, through a call the mutation scan must not miss. */
export const tableWrite = () => flags.ready
