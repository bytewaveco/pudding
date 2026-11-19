import { domain, expect, law } from "pudding"
import { couponDiscount, vatCents } from "./merged.ts"

law("FALSE: a discount never exceeds a tenth of the subtotal", domain<[boolean, string, bigint]>(), ([member, coupon, subtotal]) => {
  if (subtotal >= 0n) expect(couponDiscount(member, coupon, subtotal) * 10n <= subtotal).toBe(true)
})

law("FALSE: VAT never exceeds a fifth of the price", domain<[string, boolean, bigint]>(), ([country, express, price]) => {
  if (price >= 0n) expect(vatCents(country, express, price) * 5n <= price).toBe(true)
})

// The same functions, stated correctly, must still be proved.
law("a stacked discount is at most a fifth of the subtotal", domain<[boolean, string, bigint]>(), ([member, coupon, subtotal]) => {
  if (subtotal >= 0n) expect(couponDiscount(member, coupon, subtotal) * 5n <= subtotal).toBe(true)
})

law("only German orders pay VAT", domain<[string, boolean, bigint]>(), ([country, express, price]) => {
  if (country !== "DE") expect(vatCents(country, express, price)).toBe(0n)
})
