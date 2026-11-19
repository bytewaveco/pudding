import { domain, expect, law } from "pudding"
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
  expect(canMove(status, status)).not.toBe(true)
})

law("labels are distinct per order", domain<[Order, Order]>(), ([a, b]) => {
  if (label(a) === label(b)) expect(a).toEqual(b)
})

law("FALSE: any order ships", domain<Order>(), order => {
  expect(ship(order).status).toEqual("shipped")
})

law("FALSE: cancelled is not terminal", domain<Status>(), status => {
  expect(isTerminal(status)).toEqual(status === "shipped")
})

law("VACUOUS: contradictory guard", domain<Order>(), order => {
  if (order.status === "shipped" && !isTerminal(order.status)) expect(order.paid).toBe(true)
})

law("VACUOUS: contradictory arithmetic guard", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a < b && b < a) expect(a).toEqual(b)
})
