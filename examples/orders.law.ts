import { domain, expect, law } from "@bytewaveco/pudding"
import { canMove, isTerminal, label, ship, type Order, type Status } from "./orders.ts"

law("a paid, placed order ships", domain<Order>(), order => {
  if (order.status !== "placed" || !order.paid) return
  expect(ship(order)).toEqual({ status: "shipped", paid: true })
  expect(isTerminal(ship(order).status)).toBe(true)
})

law("nothing leaves a terminal status", domain<[Status, Status]>(), ([from, to]) => {
  if (isTerminal(from)) expect(canMove(from, to)).toBe(false)
})

law("no status moves to itself", domain<Status>(), status => {
  expect(canMove(status, status)).toBe(false)
})

law("an order is identified by its label", domain<[Order, Order]>(), ([a, b]) => {
  if (label(a) === label(b)) expect(a).toEqual(b)
})
