import { domain, expect, law } from "@bytewaveco/pudding"
import { orZero } from "./loose.ts"

// The project turns `strictNullChecks` off, so the compiler reads this domain as every bigint and no undefined.
law("FALSE: a value that may be undefined is itself", domain<bigint | undefined>(), value => {
  expect(orZero(value) === value).toBe(true)
})

// Few enough inputs to try them all, but `undefined` is not among them, so this is not every input.
law("SAMPLED: a value that may be undefined is a bigint", domain<1n | 2n | undefined>(), value => {
  expect(orZero(value) === orZero(value)).toBe(true)
})
