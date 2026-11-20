import { domain, expect, law } from "@bytewaveco/pudding"
import { orZero } from "./defaulted.ts"

// The project leaves `strict` to the compiler, which has it on: `undefined` stays in the domain.
law("a value that may be undefined gives a bigint", domain<bigint | undefined>(), value => {
  expect(orZero(value)).toBe(value === undefined ? 0n : value)
})

law("FALSE: a value that may be undefined is itself", domain<bigint | undefined>(), value => {
  expect(orZero(value) === value).toBe(true)
})
