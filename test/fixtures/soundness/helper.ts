export type Status = "draft" | "open" | "paid"
export interface Order { status: Status; total: bigint }

/** Never produces "paid". */
export function settle(order: Order): Order {
  if (order.status === "paid") return { status: "open", total: order.total }
  return order
}
