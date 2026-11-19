import { domain, expect, law } from "pudding"
import * as extras from "./extras.ts"
import { bump, deposit, describeLevel, greeting, levels, rank, weight, xor, type Account, type Bit, type Level } from "./extras.ts"

const heavier = (a: Level, b: Level) => weight(a) > weight(b)
const twice = (level: Level) => weight(level) + weight(level)

law("a higher rank is never lighter", domain<[Level, Level]>(), ([a, b]) => {
  if (rank(a) > rank(b)) expect(heavier(b, a)).toBe(false)
})

law("fallthrough cases share a rank", () => {
  expect(rank("high")).toEqual(extras.rank("max"))
})

law("every level has a positive weight", () => {
  expect(levels.every(level => weight(level) > 0n)).toBe(true)
  expect(levels.map(twice)).toEqual([2n, 4n, 8n, 8n])
  expect(levels.some(level => weight(level) > 4n)).toBe(false)
})

law("bumping never passes the top rank or drops below the current one", domain<[Level, bigint]>(), ([level, by]) => {
  expect(bump(level, by) <= 2n).toBe(true)
  expect(bump(level, by) >= rank(level)).toBe(true)
  expect(bump(level) >= rank(level)).toBe(true)
})

law("descriptions keep their quotes", domain<[Level, string]>(), ([level, quote]) => {
  expect(describeLevel(level, quote)).toEqual(`${quote}level:${level}${quote}`)
})

law("UNPROVED: different quotes give different descriptions", domain<[Level, string]>(), ([level, quote]) => {
  expect(describeLevel(level, quote)).not.toEqual(describeLevel(level, quote + "!"))
})

law("FALSE: a level name is never a quote", domain<string>(), quote => {
  expect(describeLevel("low", quote)).not.toEqual("lowlevel:lowlow")
})

law("xor is its own inverse", domain<[Bit, Bit]>(), ([a, b]) => {
  expect(xor(xor(a, b), b)).toEqual(a)
})

law("a deposit only changes the balance", domain<[Account, bigint]>(), ([account, amount]) => {
  if (amount <= 0n) return
  const { owner, balance } = deposit(account, amount)
  expect(owner).toEqual(account.owner)
  expect(balance > account.balance).toBe(true)
})

law("unusual characters survive translation", domain<Parameters<typeof greeting>[0]>(), name => {
  expect(greeting(name)).toEqual("<" + name + ">")
  expect(greeting(name) === "<😀>").toEqual(name === "😀")
})

law("FALSE: every level outweighs low", domain<Level>(), level => {
  expect(heavier(level, "low")).toBe(true)
})
