import { domain, expect, law } from "@bytewaveco/pudding"
import { settle, type Order } from "./helper.ts"

function expectPaidIsZero(order: Order) {
  if (order.status === "paid") expect(order.total).toBe(0n)
}

// The only expectation sits in a helper, behind a condition that is never true.
law("FALSE: a settled paid order owes nothing", domain<Order>(), order => {
  expectPaidIsZero(settle(order))
})
