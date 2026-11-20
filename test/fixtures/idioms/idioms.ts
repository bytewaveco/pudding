// The everyday TypeScript that business rules are written in: values that may
// be undefined, defaults, rounding, lists that are filtered and sorted, Maps,
// and callbacks that keep a running total.

export type Entry = { startAt: number; endAt?: number }
export type Step = 1 | 5 | 6 | 15

// ---------------------------------------------------------------- undefined

export function orElse(value: bigint | undefined, fallback: bigint): bigint {
  return value ?? fallback
}

export function orTruthy(value: bigint | undefined, fallback: bigint): bigint {
  return value || fallback
}

export function end(entry: Entry, now: number): number {
  return entry.endAt ?? now
}

type Node = { value: bigint; next?: Node }

export function second(node: Node | undefined): bigint | undefined {
  return node?.next?.value
}

export function third(node: Node | undefined): bigint | undefined {
  return node?.next?.next?.value
}

/** Without a node the whole chain is undefined; with one, `.value` is read of whatever `next` is. */
export function throughNext(node: Node | undefined): bigint | undefined {
  return node?.next!.value
}

/** Throws when there is no second node. */
export function secondUnsafe(node: Node): bigint {
  return node.next!.value
}

/**
 * A key that neither the object nor `Object.prototype` has reads as undefined,
 * whether or not the key is known where it is used. A key such as `"toString"`
 * finds what every object inherits instead, so no fallback applies.
 */
export function priceOf(key: string): bigint {
  return ({ a: 1n } as Record<string, bigint | undefined>)[key] ?? 0n
}

/** A property called `prototype` on an ordinary object is an ordinary property. */
export function ownPrototype(a: bigint): bigint {
  const { prototype } = { prototype: a }
  return prototype
}

export function isSet(node: Node | undefined): boolean {
  return node !== undefined
}

export function describeNode(node?: Node): string {
  if (!node) return "none"
  return node.next ? "linked" : "single"
}

// --------------------------------------------------------------- truthiness

export function stepOr(approved: number): number {
  return approved || 1
}

export function labelOr(label: string): string {
  return label || "untitled"
}

export function bothOr(a: bigint, b: bigint): bigint {
  return (a && b) || -1n
}

export function overlap(a: Entry, b: Entry): { reason: "overlap" } | undefined {
  const overlaps = a.startAt < (b.endAt ?? Infinity) && b.startAt < (a.endAt ?? Infinity)
  return overlaps ? { reason: "overlap" } : undefined
}

export function firstProblem(entry: Entry, others: Entry[], stored?: Entry) {
  if (stored?.startAt === entry.startAt && stored.endAt === entry.endAt) return undefined
  if (entry.endAt !== undefined && entry.endAt <= entry.startAt) return { reason: "order" as const }
  const found = others.find(other => other.startAt < (entry.endAt ?? Infinity) && entry.startAt < (other.endAt ?? Infinity))
  return found && { reason: "overlap" as const, with: found }
}

// ----------------------------------------------------- defaults and patterns

export function area({ width, height = width }: { width: number; height?: number }): number {
  return width * height
}

export function scale(amount: bigint, factor = 2n, offset?: bigint): bigint {
  return amount * factor + (offset ?? 0n)
}

export function without({ hidden, ...shown }: { hidden: bigint; a: bigint; b: bigint }): bigint {
  return shown.a + shown.b + (hidden - hidden)
}

export function headAndRest(list: bigint[]): bigint {
  const [head = 100n, ...rest] = list
  return rest.reduce((sum, item) => sum + item, head)
}

// ----------------------------------------------------------------- rounding

export function roundTo(minutes: number, step: Step): number {
  return Math.round(minutes / step) * step
}

export function half(n: number): number {
  return Math.round(n / 2)
}

export function third3(n: number): number {
  return Math.round(n / 3)
}

// -------------------------------------------------------------------- lists

export function positives(list: bigint[]): bigint[] {
  return list.filter(item => item > 0n)
}

export function firstNegative(list: bigint[]): bigint | undefined {
  return list.find(item => item < 0n)
}

export function expand(list: bigint[]): bigint[] {
  return list.flatMap(item => (item > 0n ? [item, item] : []))
}

/** A callback after the first match is never called, so its throw is never reached. */
export function firstOrThrow(a: bigint): bigint | undefined {
  return [a, a + 1n].find(item => {
    if (item === a) return true
    throw new Error("asked past the first match")
  })
}

export function anyOrThrow(a: bigint): boolean {
  return [a, a + 1n].some(item => {
    if (item === a) return true
    throw new Error("asked past the first match")
  })
}

export function allOrThrow(a: bigint): boolean {
  return [a, a + 1n].every(item => {
    if (item === a) return false
    throw new Error("asked past the first failure")
  })
}

export function last(list: bigint[]): bigint | undefined {
  return list.at(-1)
}

export function middle(list: bigint[]): bigint[] {
  return list.slice(1, -1)
}

export function byStart(entries: { id: string; startAt: number }[]): string[] {
  return [...entries].sort((a, b) => a.startAt - b.startAt).map(entry => entry.id)
}

export function countDown(length: number): number[] {
  return Array.from({ length }, (_, index) => length - index)
}

/** An explicit `undefined` in place of the function copies the list, as leaving it out does. */
export function copyOf(list: bigint[]): bigint[] {
  return Array.from(list, undefined as never)
}

/** A callback that ends without returning gives undefined, which counts as false. */
export function hasTwo(): boolean {
  return [1, 2, 3].some(item => {
    if (item === 2) return true
  })
}

export function grownWhileFiltered(): number[] {
  const list = [1, 2]
  return list.filter(item => {
    if (item < 3) list.push(item + 2)
    return true
  })
}

/** The only callback throws, so the call never gives an answer. */
export function someThrows(a: bigint): boolean {
  return [a].some(() => {
    throw new Error("asked")
  })
}

/** Sorts the caller's list in place and returns the smallest. */
export function smallest(list: number[]): number | undefined {
  list.sort((a, b) => a - b)
  return list[0]
}

// ------------------------------------------------------------- Map and Set

export function distinct(a: bigint, b: bigint, c: bigint): number {
  return new Set([a, b, c]).size
}

export function lookup(key: "a" | "b" | "c", fallback: bigint): bigint {
  const prices = new Map<string, bigint>([["a", 1n], ["b", 2n]])
  prices.set("a", 10n)
  return prices.get(key) ?? fallback
}

export function totalsByDay(entries: { day: number; minutes: number }[]): Map<number, { minutes: number }> {
  const days = new Map<number, { minutes: number }>()
  for (const entry of entries) {
    const day = days.get(entry.day) ?? { minutes: 0 }
    day.minutes += entry.minutes
    days.set(entry.day, day)
  }
  return days
}

export function sumOfDays(first: number, second: number, third: number): number {
  const days = totalsByDay([{ day: 1, minutes: first }, { day: 2, minutes: second }, { day: 1, minutes: third }])
  let total = 0
  for (const [, day] of days) total += day.minutes
  return total + days.size * 0
}

/** Either way one key is set, and which one depends on the condition. */
export function setEither(flag: boolean, wanted: number): bigint | undefined {
  const seen = new Map<number, bigint>()
  if (flag) seen.set(1, 10n)
  else seen.set(2, 20n)
  return seen.size === 1 ? seen.get(wanted) : -1n
}

export function setOf(a: bigint, b: bigint): Set<bigint> {
  return new Set([a, b])
}

/** Each round's callback uses the loop variable, which JavaScript copies for every round. */
export function sumOfRounds(list: bigint[]): bigint {
  let total = 0n
  for (let i = 0; i < 2; i++) total += list.map(item => item * BigInt(i)).reduce((sum, item) => sum + item, 0n)
  return total
}

export function knows(a: bigint, b: bigint, wanted: bigint): boolean {
  return new Set([a, b]).has(wanted)
}

// --------------------------------------------- callbacks with a running total

/** Shares `labor` among the entries in order: each takes what it worked, up to what is left. */
export function allocate(worked: number[], labor: number): number[] {
  let remaining = labor
  return worked.map(minutes => {
    const billed = Math.min(minutes, Math.max(0, remaining))
    remaining -= billed
    return billed
  })
}

export function tally(a: bigint, b: bigint, flag: boolean): bigint {
  let total = 0n
  const add = (amount: bigint) => {
    total += amount
    return total
  }
  const result = flag ? add(a) : add(b)
  return total + (result - result)
}

/** The callback leaves early for a negative amount, before it adds. */
export function sumOfPositives(a: bigint, b: bigint): bigint {
  let total = 0n
  const add = (amount: bigint) => {
    if (amount < 0n) return false
    total += amount
    return true
  }
  add(a)
  add(b)
  return total
}

/** `.some` stops at the first match, so later callbacks never count. */
export function countUntilNegative(a: bigint, b: bigint): bigint {
  let seen = 0n
  ;[a, b].some(item => {
    seen += 1n
    return item < 0n
  })
  return seen
}

function counter(start: bigint) {
  let count = start
  return () => {
    count += 1n
    return count
  }
}

/** The closure outlives the call that declared `count`. */
export function twice(start: bigint): bigint {
  const next = counter(start)
  next()
  return next()
}

/** The right side of `&&` only runs when the left side is true. */
export function addIf(flag: boolean, amount: bigint): bigint {
  let total = 0n
  const add = () => {
    total += amount
    return true
  }
  const ran = flag && add()
  return ran ? total : total
}
