import { domain, expect, law } from "pudding"
import { sum } from "./sum.ts"

law("FALSE: a sum of two values adds them", domain<[bigint, bigint]>(), ([a, b]) => {
  expect(sum([a, b])).toEqual(a + b)
})
