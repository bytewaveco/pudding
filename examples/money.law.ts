import { domain, expect, law } from "pudding"
import { abs, applyBasisPoints, clamp, perPart, roundToDollars } from "./money.ts"

law("clamp stays within its bounds", domain<[bigint, bigint, bigint]>(), ([x, lo, hi]) => {
  if (lo <= hi) {
    expect(clamp(x, lo, hi) >= lo).toBe(true)
    expect(clamp(x, lo, hi) <= hi).toBe(true)
  }
})

law("clamp is idempotent when the bounds are ordered", domain<[bigint, bigint, bigint]>(), ([x, lo, hi]) => {
  if (lo <= hi) expect(clamp(clamp(x, lo, hi), lo, hi)).toEqual(clamp(x, lo, hi))
})

law("abs is never negative and ignores sign", domain<bigint>(), x => {
  expect(abs(x) >= 0n).toBe(true)
  expect(abs(-x)).toEqual(abs(x))
})

law("a full rate returns the amount", domain<bigint>(), amount => {
  expect(applyBasisPoints(amount, 10_000n)).toEqual(amount)
})

law("rounding is symmetric around zero", domain<bigint>(), cents => {
  expect(roundToDollars(-cents)).toEqual(-roundToDollars(cents))
})

law("rounding never moves by more than half a dollar", domain<bigint>(), cents => {
  const difference = roundToDollars(cents) * 100n - cents
  expect(difference <= 50n && difference >= -50n).toBe(true)
})

law("nothing split into parts is nothing", domain<[bigint, bigint]>(), ([total, parts]) => {
  if (parts !== 0n) expect(perPart(total - total, parts)).toEqual(0n)
})

// The default automation does not multiply two unknowns, so this law carries its own Lean proof.
law("a product of positives is positive", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: "intro h; simp_all; exact Int.mul_pos h.1 h.2" })
