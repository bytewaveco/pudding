import { domain, expect, law } from "@bytewaveco/pudding"
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

law("FALSE: clamp is idempotent for any bounds", domain<[bigint, bigint, bigint]>(), ([x, lo, hi]) => {
  expect(clamp(clamp(x, lo, hi), lo, hi)).toEqual(clamp(x, lo, hi))
})

law("abs is never negative and ignores sign", domain<bigint>(), x => {
  expect(abs(x) >= 0n).toBe(true)
  expect(abs(-x)).toEqual(abs(x))
})

law("quotient and remainder rebuild the dividend", domain<bigint>(), x => {
  expect((x / 7n) * 7n + (x % 7n)).toEqual(x)
})

law("the remainder takes the sign of the dividend", domain<bigint>(), x => {
  if (x < 0n) expect(x % 7n <= 0n).toBe(true)
  if (x >= 0n) expect(x % 7n >= 0n).toBe(true)
})

law("a full rate returns the amount", domain<bigint>(), amount => {
  expect(applyBasisPoints(amount, 10_000n)).toEqual(amount)
})

law("rounding is symmetric around zero", domain<bigint>(), cents => {
  expect(roundToDollars(-cents)).toEqual(-roundToDollars(cents))
})

law("rounding never moves by more than half a dollar", domain<bigint>(), cents => {
  const diff = roundToDollars(cents) * 100n - cents
  expect(diff <= 50n && diff >= -50n).toBe(true)
})

law("FALSE: halving and doubling returns the input", domain<bigint>(), x => {
  expect((x / 2n) * 2n).toEqual(x)
})

law("FALSE: dividing by any number of parts is safe", domain<[bigint, bigint]>(), ([total, parts]) => {
  expect(perPart(total, parts) * parts <= total || total < 0n || parts < 0n).toBe(true)
})

law("dividing by a non-zero number of parts is safe", domain<[bigint, bigint]>(), ([total, parts]) => {
  if (parts !== 0n) expect(perPart(total - total, parts)).toEqual(0n)
})

law("UNPROVED: a product of positives is positive", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
})

law("a product of positives is positive, with a supplied proof", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: "intro h; simp_all; exact Int.mul_pos h.1 h.2" })

law("a fixed example", () => {
  expect(applyBasisPoints(200n, 250n)).toEqual(5n)
  expect(roundToDollars(-150n)).toEqual(-2n)
})
