import { domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { settle } from "./growth.ts"

law("settling never grows the value", domain<Integer<0, 1000>>(), start => {
  expect(settle(start) <= start).toBe(true)
})
