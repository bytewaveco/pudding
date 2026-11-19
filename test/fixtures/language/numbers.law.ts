import { describe, domain, expect, law, type Integer } from "pudding"
import { average, clampPercent, countdown, label, minutes, pageCount, pageOf, parity, sumIndexed, sumTo, toCents } from "./numbers.ts"

describe("whole numbers", () => {
  law("pages cover every item without an empty page", domain<[Integer<0, 1000000>, Integer<1, 12>]>(), ([total, size]) => {
    const pages = pageCount(total, size)
    expect(pages * size >= total).toBe(true)
    expect((pages - 1) * size < total || total === 0).toBe(true)
  })

  law("an index belongs to exactly one page", domain<[Integer<0, 1000000>, Integer<1, 12>]>(), ([index, size]) => {
    const page = pageOf(index, size)
    expect(page * size <= index && index < (page + 1) * size).toBe(true)
  })

  law("floor rounds toward minus infinity for negative indexes", () => {
    expect(pageOf(-1, 10)).toEqual(-1)
    expect(pageOf(-10, 10)).toEqual(-1)
    expect(pageOf(-11, 10)).toEqual(-2)
    expect(pageCount(-1, 10)).toEqual(0)
    expect(pageCount(11, 10)).toEqual(2)
    expect(Math.trunc(-7 / 2)).toEqual(-3)
    expect(Math.trunc(7 / -2)).toEqual(-3)
  })

  law("a clamped percentage is a percentage", domain<Integer>(), value => {
    expect(clampPercent(value) >= 0 && clampPercent(value) <= 100).toBe(true)
    expect(clampPercent(clampPercent(value))).toEqual(clampPercent(value))
  })

  law("parity alternates", domain<Integer<-1000000, 1000000>>(), value => {
    expect(parity(value + 1)).not.toEqual(parity(value))
    expect(parity(-value)).toEqual(parity(value))
  })

  law("small ranges are checked case by case", domain<[Integer<0, 23>, Integer<0, 59>]>(), ([hours, extra]) => {
    expect(minutes(hours, extra) < 24 * 60).toBe(true)
    expect(Math.floor(minutes(hours, extra) / 60)).toEqual(hours)
    expect(minutes(hours, extra) % 60).toEqual(extra)
  })

  law("literal number unions are inputs too", domain<1 | 2 | 12>(), count => {
    expect(label(count)).toEqual(count === 1 ? "1 item" : count === 2 ? "2 items" : "12 items")
  })

  law("bigint amounts convert when they are small enough", domain<bigint>(), dollars => {
    if (dollars >= 0n && dollars <= 1000000n) expect(toCents(dollars) % 100).toEqual(0)
  })

  law("FALSE: adding one always grows a number", domain<Integer>(), value => {
    expect(value + 1 > value).toBe(true)
  })

  law("FALSE: pages never divide by zero", domain<[Integer<0, 100>, Integer<0, 10>]>(), ([total, size]) => {
    expect(pageCount(total, size) >= 0).toBe(true)
  })

  law("FALSE: an index is on the page before its own", domain<[Integer<0, 1000000>, Integer<1, 12>]>(), ([index, size]) => {
    expect(pageOf(index, size) * size < index).toBe(true)
  })

  law("FALSE: any bigint converts to a number", domain<bigint>(), dollars => {
    expect(toCents(dollars) % 100).toEqual(0)
  })
})

describe("counted loops", () => {
  law("a counting loop sums a known range", () => {
    expect(sumTo(10)).toEqual(55)
    expect(sumTo(0)).toEqual(0)
    expect(countdown(7)).toEqual(7)
  })

  law("an indexed loop reads every element", domain<[Integer<-1000, 1000>, Integer<-1000, 1000>, Integer<-1000, 1000>]>(), ([a, b, c]) => {
    expect(sumIndexed([a, b, c])).toEqual(a + b + c)
    expect([a, b, c].length).toEqual(3)
  })

  law("SAMPLED: a loop bounded by a large input cannot be unrolled", domain<Integer<0, 100000>>(), limit => {
    expect(sumTo(limit) >= limit).toBe(true)
  })

  law("a loop bounded by a small input is unrolled for each of its values", domain<Integer<0, 20>>(), limit => {
    expect(sumTo(limit) * 2).toEqual(limit * (limit + 1))
  })

  law("SAMPLED: plain division is refused", domain<[Integer<0, 100>, Integer<0, 100>]>(), ([a, b]) => {
    expect(average(a, b) * 2).toEqual(a + b)
  })
})
