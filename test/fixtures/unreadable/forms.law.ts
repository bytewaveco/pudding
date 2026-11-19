import { describe, domain, expect, law, law as register } from "@bytewaveco/pudding"

// A law that is not an ordinary synchronous function with one plain parameter.
law("FALSE: an async law has finished", async () => {
  expect(true).toBe(true)
  return { then: (_: (value: boolean) => void) => { throw Error("completion failed") } }
})
law("FALSE: a rest parameter is the tuple", domain<[true, true]>(), (...args) => expect<number>(args.length).toBe(2))

// A local function that only shares the library's name.
describe("suite", () => {
  function law(name: string, body: () => void) {
    register(name, () => { body(); expect(false).toBe(true) })
  }
  law("FALSE: passes the suite check", () => expect(true).toBe(true))
})
