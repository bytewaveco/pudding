// Assignments made by a construct nested in an `if` that has no early exit.

/** Members can stack coupons: VIP20 also includes the MEMBER10 discount, by falling through. */
export function couponDiscount(member: boolean, coupon: string, subtotal: bigint): bigint {
  let discount = 0n
  if (member) {
    switch (coupon) {
      case "VIP20":
        discount += subtotal / 10n
      case "MEMBER10":
        discount += subtotal / 10n
    }
  }
  return discount
}

/** German orders pay 19% VAT on the item and, when express, on the 500-cent express fee. */
export function vatCents(country: string, express: boolean, price: bigint): bigint {
  const charges = express ? [price, 500n] : [price]
  let vat = 0n
  if (country === "DE") {
    for (const charge of charges) vat += (charge * 19n) / 100n
  }
  return vat
}
