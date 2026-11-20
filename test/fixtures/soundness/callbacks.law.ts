import { domain, expect, law } from "@bytewaveco/pudding"
import {
  callAfterChain, compound, defaultBeforeBody, filterStale, flatShared, fromList, fromSet, listPatternBeforeItsName, missingMethod, patternBeforeItsName, patternPastEnd,
  perRound, restoredBySome, spreadThenPush,
} from "./callbacks.ts"

law("FALSE: a compound assignment reads its variable after the right side ran", domain<bigint>(), a => {
  expect(compound(a)).toBe(10n + a)
})

law("FALSE: every round of a for loop shares one variable", () => {
  expect(perRound()).toBe(3)
})

law("FALSE: a spread sees what a later element adds", domain<bigint>(), a => {
  expect(spreadThenPush(a)).toEqual([a, 2n, 0n])
})

law("FALSE: a call after an optional chain gives undefined", () => {
  expect(callAfterChain()).toBe(undefined)
})

law("FALSE: filter keeps what its callback wrote", domain<bigint>(), a => {
  expect(filterStale(a)).toBe(99n)
})

law("FALSE: flatMap spreads every result after the last callback", () => {
  expect(flatShared()).toBe(4)
})

law("FALSE: Array.from misses what its function adds to a Set", () => {
  expect(fromSet()).toBe(1)
})

law("FALSE: Array.from misses what its function pushes", () => {
  expect(fromList()).toBe(1)
})

law("FALSE: a pattern reads on after the end of its list", domain<bigint>(), a => {
  expect(patternPastEnd(a)).toBe(9n)
})

law("FALSE: a default in a loop's pattern reads the variable outside the loop", domain<{ c: 1 | 2 }>(), ({ c }) => {
  expect(patternBeforeItsName(c)).toBe(100 + c)
})

law("FALSE: a default in a loop's list pattern reads the variable outside the loop", domain<{ c: 1 | 2 }>(), ({ c }) => {
  expect(listPatternBeforeItsName(c)).toBe(100 + c)
})

law("FALSE: a default calls a function its body declares", domain<{ c: 1 | 2 }>(), ({ c }) => {
  expect(defaultBeforeBody(c)).toBe(1 + c)
})

const b = 100n

law("FALSE: a default in a law's pattern reads the variable outside the law", domain<{ f?: undefined; a?: undefined; b: 1n | 2n }>(), ({ f = () => b, a = f(), b }) => {
  expect(a as bigint).toBe(100n)
  expect(b === 1n || b === 2n).toBe(true)
})

law("FALSE: a callback .some never reaches puts the variable back", () => {
  expect(restoredBySome()).toBe(0n)
})

law("FALSE: a method the object does not have gives a value", () => {
  expect(missingMethod()).toBe(0n)
})
