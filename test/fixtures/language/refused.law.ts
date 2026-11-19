import { domain, expect, law } from "@bytewaveco/pudding"
import { chained, makeCounter, mutatesObject, pushes, readsLater, whileLoop } from "./refused.ts"

law("SAMPLED: a closure that writes an outer variable", domain<bigint>(), start => {
  expect(makeCounter(start)).toEqual(start + 1n)
})

law("CHECKED: a closure that reads a reassigned variable", domain<boolean>(), flag => {
  expect(readsLater(flag)).toEqual(flag ? 2n : 1n)
})

law("an object the function made itself may be changed in place", domain<bigint>(), amount => {
  expect(mutatesObject(amount)).toEqual(amount)
})

law("an array the function made itself may be pushed to", domain<bigint>(), amount => {
  expect(pushes(amount)).toEqual(amount)
})

law("SAMPLED: assignment used as a value", domain<bigint>(), amount => {
  expect(chained(amount)).toEqual(amount + amount)
})

law("a while loop bounded by a small input", domain<1n | 2n | 3n>(), limit => {
  expect(whileLoop(limit)).toEqual(limit)
})
