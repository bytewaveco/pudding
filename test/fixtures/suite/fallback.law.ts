import { domain, expect, law } from "pudding"
import { initials, total } from "./fallback.ts"

law("SAMPLED: the total of a pair is their sum", domain<[bigint, bigint]>(), ([a, b]) => {
  expect(total([a, b])).toEqual(a + b)
})

law("CHECKED: initials are one character", domain<"ada" | "grace">(), name => {
  expect(initials(name) === "A" || initials(name) === "G").toBe(true)
})

law("FALSE when executed: totals ignore the first amount", domain<[bigint, bigint]>(), ([a, b]) => {
  expect(total([a, b])).toEqual(b)
})
