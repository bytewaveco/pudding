import { describe, domain, expect, law } from "@bytewaveco/pudding"
import {
  assertPositive, bump, cents, countPositive, describeTier, discount, firstNegative, indexOfZero, journalTotals, largest, signed, total,
  type Line, type Tier,
} from "./imperative.ts"

describe("loops", () => {
  law("a total is the sum of its parts", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    expect(total([a, b, c])).toEqual(a + b + c)
    expect(total([])).toEqual(0n)
  })

  law("the largest value is at least every value and is one of them", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    const most = largest([a, b, c])
    expect(most >= a && most >= b && most >= c).toBe(true)
    expect(most === a || most === b || most === c).toBe(true)
  })

  law("continue skips what follows it", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(countPositive([a, b])).toEqual((a > 0n ? 1n : 0n) + (b > 0n ? 1n : 0n))
  })

  law("break stops at the first match", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(firstNegative([a, b])).toEqual(a < 0n ? a : b < 0n ? b : 0n)
  })

  law("return leaves the loop with the running index", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    expect(indexOfZero([a, b, c])).toEqual(a === 0n ? 0n : b === 0n ? 1n : c === 0n ? 2n : -1n)
  })

  law("a loop inside a law checks every element", domain<bigint>(), base => {
    let running = base
    for (const step of [1n, 2n, 3n]) {
      running += step
      expect(running > base).toBe(true)
    }
    expect(running).toEqual(base + 6n)
  })

  law("FALSE: the total ignores its last part", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(total([a, b])).toEqual(a)
  })

  law("FALSE: break keeps looking after the first match", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(firstNegative([a, b])).toEqual(b < 0n ? b : a < 0n ? a : 0n)
  })
})

describe("reassignment", () => {
  law("discounts follow the tier and loyalty", domain<[Tier, bigint, boolean]>(), ([tier, amount, loyal]) => {
    const rate = (tier === "gold" ? 10n : tier === "silver" ? 5n : 0n) + (loyal ? 2n : 0n)
    expect(discount(tier, amount, loyal)).toEqual(amount - (amount * rate) / 100n)
  })

  law("a discount never raises a non-negative price", domain<[Tier, bigint, boolean]>(), ([tier, amount, loyal]) => {
    if (amount >= 0n) expect(discount(tier, amount, loyal) <= amount).toBe(true)
  })

  law("switch branches assign and break", domain<Tier>(), tier => {
    expect(describeTier(tier)).toEqual("tier:" + tier)
  })

  law("parameters can be reassigned and updated", domain<[bigint, Tier]>(), ([value, times]) => {
    expect(bump(value, times)).toEqual(value + (times === "gold" ? 2n : times === "silver" ? 0n : -1n))
  })

  law("FALSE: loyalty is ignored", domain<[bigint, boolean]>(), ([amount, loyal]) => {
    expect(discount("gold", amount, loyal)).toEqual(amount - (amount * 10n) / 100n)
  })
})

describe("reduce", () => {
  law("journal totals add each side", domain<[Line, Line]>(), ([first, second]) => {
    expect(journalTotals([first, second])).toEqual({ debits: first.debit + second.debit, credits: first.credit + second.credit })
  })

  law("balanced lines give balanced totals", domain<[bigint, bigint]>(), ([a, b]) => {
    const totals = journalTotals([{ debit: a, credit: 0n }, { debit: b, credit: 0n }, { debit: 0n, credit: a + b }])
    expect(totals.debits).toEqual(totals.credits)
  })

  law("FALSE: credits are counted as debits", domain<Line>(), line => {
    expect(journalTotals([line]).debits).toEqual(line.debit + line.credit)
  })
})

describe("bigint to text", () => {
  law("fixed amounts print as expected", () => {
    expect(cents(-1234n)).toEqual("-12.34c")
    expect(cents(5n)).toEqual("0.5c")
    expect(signed(-7n)).toEqual("-7!-7")
    expect(signed(0n)).toEqual("0!0")
  })

  law("toString and String agree", domain<bigint>(), value => {
    expect(value.toString()).toEqual(String(value))
    expect(`${value}`).toEqual(String(value))
  })

  law("small amounts print with their sign", domain<-1n | 0n | 12n | 305n>(), value => {
    expect(cents(value * 100n)).toEqual(`${value}.0c`)
  })

  law("FALSE: every amount prints two cent digits", domain<3n | 45n>(), value => {
    expect(cents(value)).toEqual(value === 3n ? "0.03c" : "0.45c")
  })
})

describe("helpers that assert", () => {
  const within = (value: bigint, low: bigint, high: bigint) => {
    expect(value >= low).toBe(true)
    expect(value <= high).toBe(true)
  }

  law("an asserting helper is followed into", domain<Tier>(), tier => {
    within(discount(tier, 100n, true), 88n, 98n)
  })

  law("a void function that returns normally is fine", domain<bigint>(), value => {
    if (value > 0n) {
      assertPositive(value)
      expect(value >= 1n).toBe(true)
    }
  })

  law("FALSE: the helper's bounds are too tight", domain<Tier>(), tier => {
    within(discount(tier, 100n, false), 91n, 99n)
  })

  law("FALSE: a void function that throws is reported", domain<bigint>(), value => {
    assertPositive(value)
    expect(value >= 1n).toBe(true)
  })
})
