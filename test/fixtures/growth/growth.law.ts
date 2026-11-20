import { domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { huge, settle } from "./growth.ts"

law("settling never grows the value", domain<Integer<0, 1000>>(), start => {
  expect(settle(start) <= start).toBe(true)
})

law("huge loop still stays above its input for positives", domain<bigint>(), start => {
  if (start >= 0n) expect(huge(start) >= start).toBe(true)
})
