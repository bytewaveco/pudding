import { domain, expect, law } from "pudding"
import "./configure-setup.ts"
import { fee, toCents } from "./configured.ts"

law("FALSE: euros convert at 90 cents", domain<bigint>(), units => {
  expect(toCents("eur", units)).toBe(units * 90n)
})

law("FALSE: pro orders cost 2 each", domain<bigint>(), orders => {
  expect(fee("pro", orders)).toBe(orders * 2n)
})
