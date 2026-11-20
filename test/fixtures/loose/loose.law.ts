import { domain, expect, law } from "@bytewaveco/pudding"
import { orZero } from "./loose.ts"

// The project turns `strictNullChecks` off, so the compiler reads this domain as every bigint and no undefined.
law("FALSE: a value that may be undefined is itself", domain<bigint | undefined>(), value => {
  expect(orZero(value) === value).toBe(true)
})

law("SAMPLED: a value that may be undefined is a bigint", domain<bigint | undefined>(), value => {
  expect(orZero(value) === orZero(value)).toBe(true)
})
