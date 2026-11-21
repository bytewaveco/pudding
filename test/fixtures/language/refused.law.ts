import { domain, expect, law } from "@bytewaveco/pudding"
import { chained, countsLater, makeCounter, mutatesObject, pushes, readsLater, whileLoop } from "./refused.ts"

law("a closure may assign to a variable of the function that is still running", domain<bigint>(), start => {
  expect(makeCounter(start)).toEqual(start + 1n)
})

law("a closure reads a reassigned variable as it is when called", domain<boolean>(), flag => {
  expect(readsLater(flag)).toEqual(flag ? 2n : 1n)
})

law("a closure that outlives the variable it assigns is proved", domain<bigint>(), start => {
  expect(countsLater(start)).toEqual(start + 2n)
})

law("a closure reading a later-declared const succeeds when the early call is unreachable", domain<bigint>(), x => {
  const compute = (n: bigint): bigint => {
    const readBase = () => base + n
    if (n > 0n && n < 0n) return readBase()
    const base = 10n
    return readBase()
  }
  expect(compute(x)).toEqual(10n + x)
})

law("FALSE: a reachable call before declaration throws", domain<bigint>(), x => {
  const compute = (n: bigint): bigint => {
    const readBase = () => base + n
    if (n < 0n) return readBase()
    const base = 10n
    return readBase()
  }
  expect(compute(x)).toEqual(10n + x)
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
