import { describe, domain, expect, law, type Integer } from "@bytewaveco/pudding"
import {
  addIf, allocate, area, bothOr, byStart, countDown, countUntilNegative, describeNode, distinct, end, expand, firstNegative, firstProblem, half, headAndRest,
  isSet, knows, labelOr, last, lookup, middle, orElse, orTruthy, overlap, positives, roundTo, scale, second, secondUnsafe, setEither, setOf, smallest, stepOr,
  sumOfDays, sumOfPositives, sumOfRounds, tally, third, third3, throughNext, twice, without, type Step,
} from "./idioms.ts"

type Instant = Integer<0, 1_000_000_000_000>
type Minutes = Integer<0, 100_000>

describe("values that may be undefined", () => {
  law("?? takes the fallback only for undefined", domain<{ value: bigint | undefined; fallback: bigint }>(), ({ value, fallback }) => {
    expect(orElse(value, fallback)).toBe(value === undefined ? fallback : value)
  })

  law("FALSE: ?? and || agree", domain<{ value: bigint | undefined; fallback: bigint }>(), ({ value, fallback }) => {
    expect(orElse(value, fallback)).toBe(orTruthy(value, fallback))
  })

  law("a property left out reads as undefined", domain<{ startAt: Instant; endAt?: Instant; now: Instant }>(), ({ now, ...entry }) => {
    expect(end(entry, now)).toBe(entry.endAt === undefined ? now : entry.endAt)
  })

  law("FALSE: an entry always ends when it says", domain<{ startAt: Instant; endAt?: Instant; now: Instant }>(), ({ now, ...entry }) => {
    expect(end(entry, now) === entry.endAt).toBe(true)
  })

  law("?. stops at the first missing link", domain<{ a: bigint; b: bigint; links: 0 | 1 | 2 | 3 }>(), ({ a, b, links }) => {
    const tail = { value: b }
    const node = links === 0 ? undefined : links === 1 ? { value: a } : links === 2 ? { value: a, next: tail } : { value: a, next: { value: a, next: tail } }
    expect(second(node)).toBe(links === 2 ? b : links === 3 ? a : undefined)
    expect(third(node)).toBe(links === 3 ? b : undefined)
  })

  law("what follows a ?. is skipped with it", domain<{ a: bigint; linked: boolean }>(), ({ a, linked }) => {
    expect(throughNext(linked ? { value: a, next: { value: a } } : undefined)).toBe(linked ? a : undefined)
  })

  law("FALSE: what follows a ?. never throws", domain<{ a: bigint; linked: boolean }>(), ({ a, linked }) => {
    expect(throughNext(linked ? { value: a, next: { value: a } } : { value: a })).toBe(linked ? a : undefined)
  })

  law("FALSE: there is always a second node", domain<{ a: bigint; linked: boolean }>(), ({ a, linked }) => {
    expect(secondUnsafe(linked ? { value: a, next: { value: a } } : { value: a })).toBe(a)
  })

  law("an object is never undefined, and counts as true", domain<{ a: bigint; links: 0 | 1 | 2 }>(), ({ a, links }) => {
    const node = links === 0 ? undefined : links === 1 ? { value: a } : { value: a, next: { value: a } }
    expect(isSet(node)).toBe(links !== 0)
    expect(describeNode(node)).toBe(links === 0 ? "none" : links === 1 ? "single" : "linked")
    expect(describeNode()).toBe("none")
    expect(node === undefined).toBe(links === 0)
    if (links !== 0) expect(node).not.toEqual(undefined)
  })
})

describe("truthiness", () => {
  law("|| replaces zero and the empty string", domain<{ approved: Integer; label: "" | "week" }>(), ({ approved, label }) => {
    expect(stepOr(approved)).toBe(approved === 0 ? 1 : approved)
    expect(labelOr(label)).toBe(label === "" ? "untitled" : label)
  })

  law("FALSE: || keeps zero", domain<Integer>(), approved => {
    expect(stepOr(approved)).toBe(approved)
  })

  law("&& gives its left side when that is zero, and its right side otherwise", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(bothOr(a, b)).toBe(a === 0n || b === 0n ? -1n : b)
  })

  law("FALSE: && gives its left side", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(bothOr(a, b)).toBe(a === 0n ? -1n : a)
  })

  law("an entry without an end runs on: Infinity is past every instant", domain<{ a: Instant; b: Instant; bEnd: Instant }>(), ({ a, b, bEnd }) => {
    expect(overlap({ startAt: a }, { startAt: b })).toEqual({ reason: "overlap" })
    expect(overlap({ startAt: a }, { startAt: b, endAt: bEnd }) === undefined).toBe(bEnd <= a)
  })

  law("FALSE: two clocks never overlap", domain<{ a: Instant; b: Instant }>(), ({ a, b }) => {
    expect(overlap({ startAt: a }, { startAt: b })).toBe(undefined)
  })

  law("a rule that reads optional values, finds, and returns an object or undefined", domain<{ start: Instant; length: Integer<1, 1000>; other: Instant }>(), ({ start, length, other }) => {
    const entry = { startAt: start, endAt: start + length }
    expect(firstProblem(entry, [], entry)).toBe(undefined)
    expect(firstProblem({ startAt: start, endAt: start }, [])?.reason).toBe("order")
    expect(firstProblem(entry, [{ startAt: other, endAt: other + 1 }])?.reason).toBe(other < start + length && start < other + 1 ? "overlap" : undefined)
  })

  law("FALSE: an entry that touches another overlaps it", domain<{ start: Instant; length: Integer<1, 1000> }>(), ({ start, length }) => {
    expect(firstProblem({ startAt: start, endAt: start + length }, [{ startAt: start + length, endAt: start + length + 1 }])?.reason).toBe("overlap")
  })
})

describe("defaults and patterns", () => {
  law("a default fills in what is left out or undefined", domain<{ width: Integer<0, 12>; height?: Integer<0, 12> }>(), size => {
    expect(area(size)).toBe(size.width * (size.height === undefined ? size.width : size.height))
  })

  law("FALSE: a missing height is zero", domain<{ width: Integer<0, 12>; height?: Integer<0, 12> }>(), size => {
    expect(area(size)).toBe(size.height === undefined ? 0 : size.width * size.height)
  })

  law("parameters a call leaves out are undefined", domain<{ amount: bigint; factor: bigint | undefined; offset: bigint }>(), ({ amount, factor, offset }) => {
    expect(scale(amount)).toBe(amount * 2n)
    expect(scale(amount, factor, offset)).toBe(amount * (factor === undefined ? 2n : factor) + offset)
  })

  law("rest patterns hold what the named parts left", domain<{ hidden: bigint; a: bigint; b: bigint }>(), parts => {
    expect(without(parts)).toBe(parts.a + parts.b)
    expect(headAndRest([parts.a, parts.b, parts.hidden])).toBe(parts.a + parts.b + parts.hidden)
    expect(headAndRest([])).toBe(100n)
  })

  law("FALSE: the head of an empty list is zero", () => {
    expect(headAndRest([])).toBe(0n)
  })
})

describe("rounding", () => {
  law("Math.round of a quotient is the nearest multiple, a half going up", domain<{ minutes: Minutes; step: Step }>(), ({ minutes, step }) => {
    const rounded = roundTo(minutes, step)
    expect(rounded % step).toBe(0)
    expect(minutes * 2 - step < rounded * 2 && rounded * 2 <= minutes * 2 + step).toBe(true)
  })

  law("a negative half rounds up, toward zero", domain<Integer<-100_000, 100_000>>(), n => {
    expect(half(n)).toBe(Math.floor((n + 1) / 2))
  })

  law("FALSE: a half rounds away from zero", domain<Integer<-100_000, 100_000>>(), n => {
    expect(half(n)).toBe(n < 0 ? -half(-n) : half(n))
  })

  law("FALSE: a half rounds down", domain<{ minutes: Minutes; step: Step }>(), ({ minutes, step }) => {
    expect(roundTo(minutes, step) * 2 < minutes * 2 + step).toBe(true)
  })

  law("FALSE: any whole number rounds exactly", domain<Integer>(), n => {
    expect(third3(n) * 3 - n <= 1).toBe(true)
  })
})

describe("lists", () => {
  law("filter keeps what passes, in order", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    const kept = positives([a, b, c])
    expect(kept.length).toBe((a > 0n ? 1 : 0) + (b > 0n ? 1 : 0) + (c > 0n ? 1 : 0))
    expect(kept.every(item => item > 0n)).toBe(true)
    if (a > 0n && c > 0n) expect(kept).toEqual(b > 0n ? [a, b, c] : [a, c])
  })

  law("FALSE: filter keeps the list as long as it was", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(positives([a, b]).length).toBe(2)
  })

  law("find gives the first match or undefined", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(firstNegative([a, b])).toBe(a < 0n ? a : b < 0n ? b : undefined)
  })

  law("FALSE: find gives the last match", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(firstNegative([a, b])).toBe(b < 0n ? b : a < 0n ? a : undefined)
  })

  law("flatMap joins what each element gives", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(expand([a, b]).length).toBe((a > 0n ? 2 : 0) + (b > 0n ? 2 : 0))
    if (a > 0n && b <= 0n) expect(expand([a, b])).toEqual([a, a])
  })

  law("at and slice count from either end", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    expect(last([a, b, c])).toBe(c)
    expect(last([])).toBe(undefined)
    expect(middle([a, b, c])).toEqual([b])
    expect(middle([a])).toEqual([])
  })

  law("sort puts entries in the order of their keys, and keeps ties as they were", domain<"x" | "y">(), id => {
    expect(byStart([{ id: "late", startAt: 9 }, { id, startAt: 3 }, { id: "tie", startAt: 3 }, { id: "early", startAt: 1 }])).toEqual(["early", id, "tie", "late"])
  })

  law("FALSE: sort reverses ties", () => {
    expect(byStart([{ id: "first", startAt: 3 }, { id: "second", startAt: 3 }])).toEqual(["second", "first"])
  })

  law("sorting in place changes the list it was given", () => {
    const list = [3, 1, 2]
    expect(smallest(list)).toBe(1)
    expect(list).toEqual([1, 2, 3])
  })

  law("SAMPLED: sorting by keys that are not known", domain<[Integer, Integer]>(), ([a, b]) => {
    expect(byStart([{ id: "a", startAt: a }, { id: "b", startAt: b }]).length).toBe(2)
  })

  law("Array.from builds a list of a known length", () => {
    expect(countDown(3)).toEqual([3, 2, 1])
    expect(countDown(0)).toEqual([])
  })
})

describe("Map and Set", () => {
  law("a Set counts each value once", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    expect(distinct(a, b, c)).toBe(a === b && b === c ? 1 : a === b || b === c || a === c ? 2 : 3)
    expect(knows(a, b, c)).toBe(c === a || c === b)
  })

  law("FALSE: a Set counts every value", domain<[bigint, bigint, bigint]>(), ([a, b, c]) => {
    expect(distinct(a, b, c)).toBe(3)
  })

  law("a Map gives the latest value of a key, or undefined", domain<{ key: "a" | "b" | "c"; fallback: bigint }>(), ({ key, fallback }) => {
    expect(lookup(key, fallback)).toBe(key === "a" ? 10n : key === "b" ? 2n : fallback)
  })

  law("FALSE: a Map keeps the first value of a key", domain<bigint>(), fallback => {
    expect(lookup("a", fallback)).toBe(1n)
  })

  law("objects held in a Map are changed in place, and a loop goes through each key once", domain<[Minutes, Minutes, Minutes]>(), ([first, second, third]) => {
    expect(sumOfDays(first, second, third)).toBe(first + second + third)
  })

  law("a key set on both sides of a condition is the key of the side taken", domain<{ flag: boolean; wanted: 1 | 2 | 3 }>(), ({ flag, wanted }) => {
    expect(setEither(flag, wanted)).toBe(flag ? (wanted === 1 ? 10n : undefined) : wanted === 2 ? 20n : undefined)
  })

  law("FALSE: a key set on one side of a condition is always there", domain<boolean>(), flag => {
    expect(setEither(flag, 1)).toBe(10n)
  })

  law("CHECKED: Sets are compared by what they hold when a law is executed", domain<{ a: 1n | 2n; b: 1n | 2n }>(), ({ a, b }) => {
    expect(setOf(a, b)).toEqual(setOf(b, a))
    expect(setOf(a, b)).not.toEqual(new Set([3n]))
  })

  law("FALSE when executed: two Sets are equal whatever they hold", domain<{ a: 1n | 2n; b: 1n | 2n }>(), ({ a, b }) => {
    expect(setOf(a, b)).toEqual(new Set([1n, 2n]))
  })

  law("SAMPLED: a callback that uses the variable of a for loop around it", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(sumOfRounds([a, b])).toBe(a + b)
  })

  law("FALSE: a day's total is its last entry", domain<[Minutes, Minutes, Minutes]>(), ([first, second, third]) => {
    expect(sumOfDays(first, second, third)).toBe(second + third)
  })
})

describe("callbacks with a running total", () => {
  law("a callback may update a variable of the function that is running", domain<{ first: Minutes; second: Minutes; labor: Minutes }>(), ({ first, second, labor }) => {
    const [a, b] = allocate([first, second], labor)
    expect(a).toBe(Math.min(first, labor))
    expect(a! + b!).toBe(Math.min(first + second, labor))
  })

  law("FALSE: every entry bills all of the labor", domain<{ first: Minutes; second: Minutes; labor: Minutes }>(), ({ first, second, labor }) => {
    expect(allocate([first, second], labor)[1]).toBe(Math.min(second, labor))
  })

  law("an update made on one side of a condition is kept for that side only", domain<{ a: bigint; b: bigint; flag: boolean }>(), ({ a, b, flag }) => {
    expect(tally(a, b, flag)).toBe(flag ? a : b)
  })

  law("FALSE: an update made in a condition is dropped", domain<{ a: bigint; b: bigint; flag: boolean }>(), ({ a, b, flag }) => {
    expect(tally(a, b, flag)).toBe(0n)
  })

  law("FALSE: both sides of a condition update", domain<{ a: bigint; b: bigint; flag: boolean }>(), ({ a, b, flag }) => {
    expect(tally(a, b, flag)).toBe(a + b)
  })

  law("an update after an early return happens only on the path that reaches it", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(sumOfPositives(a, b)).toBe((a < 0n ? 0n : a) + (b < 0n ? 0n : b))
  })

  law("FALSE: an early return still updates", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(sumOfPositives(a, b)).toBe(a + b)
  })

  law("FALSE: an early return undoes the updates before it", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(sumOfPositives(a, b)).toBe(b < 0n ? 0n : (a < 0n ? 0n : a) + b)
  })

  law("SAMPLED: a callback of .some that updates a variable", domain<[bigint, bigint]>(), ([a, b]) => {
    expect(countUntilNegative(a, b)).toBe(a < 0n ? 1n : 2n)
  })

  law("SAMPLED: a closure that outlives the variable it updates", domain<bigint>(), start => {
    expect(twice(start)).toBe(start + 2n)
  })

  law("SAMPLED: an update on the right side of &&", domain<{ flag: boolean; amount: bigint }>(), ({ flag, amount }) => {
    expect(addIf(flag, amount)).toBe(flag ? amount : 0n)
  })
})
