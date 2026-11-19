export type Currency = "usd" | "eur"

const rates = { usd: 100n, eur: 90n }

/** Another module may call this while it loads. */
export function configureRates(overrides: Partial<Record<Currency, bigint>>): void {
  Object.assign(rates, overrides)
}

export function toCents(currency: Currency, units: bigint): bigint {
  return units * rates[currency]
}

const fees = { basic: 5n, pro: 2n }
const admin = {
  discountPro: () => {
    Object.assign(fees, { pro: 1n })
  },
}
// Runs while the module loads, through a method of a local object.
export const launchPromo = admin.discountPro()

export function fee(plan: "basic" | "pro", orders: bigint): bigint {
  return orders * fees[plan]
}
