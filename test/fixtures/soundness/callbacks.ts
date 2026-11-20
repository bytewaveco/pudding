// A function called in the middle of an expression can change what the rest
// of the expression reads. Each of these depends on JavaScript's order.

/** `total += f()` reads `total` before `f` runs. */
export function compound(a: bigint): bigint {
  let total = 1n
  const bump = () => {
    total = 10n
    return a
  }
  total += bump()
  return total
}

/** `for (let i …)` gives every round its own `i`. */
export function perRound(): number {
  const reads: (() => number)[] = []
  for (let i = 0; i < 3; i++) reads.push(() => i)
  return reads[0]!()
}

/** A spread copies the list where it stands, before later elements run. */
export function spreadThenPush(a: bigint): bigint[] {
  const list = [a]
  const add = () => {
    list.push(2n)
    return 0n
  }
  return [...list, add()]
}

/** A call that follows an optional chain without a `?.` of its own still throws on undefined. */
export function callAfterChain(): bigint | undefined {
  const holder: { inner?: { run?: () => bigint } } = { inner: {} }
  return holder.inner?.run!()
}

/** `.filter` keeps the element it read before calling the callback. */
export function filterStale(a: bigint): bigint {
  const list = [a, 2n]
  const kept = list.filter(() => {
    list[0] = 99n
    return true
  })
  return kept[0]!
}

/** `.flatMap` spreads each result as soon as its callback returns. */
export function flatShared(): number {
  const shared = [1n]
  const out = [0n, 0n].flatMap((_, index) => {
    if (index === 1) shared.push(2n)
    return shared
  })
  return out.length
}

/** `Array.from` walks its source as it goes, so it sees what its function adds. */
export function fromSet(): number {
  const seen = new Set<bigint>([1n])
  return Array.from(seen, item => {
    if (item < 3n) seen.add(item + 1n)
    return item
  }).length
}

export function fromList(): number {
  const list = [1n]
  return Array.from(list, item => {
    if (item < 3n) list.push(item + 1n)
    return item
  }).length
}

/** A pattern that has run past the end of a list reads nothing more from it. */
export function patternPastEnd(a: bigint): bigint | undefined {
  const list: bigint[] = [a]
  const grow = () => {
    list.push(8n, 9n)
    return 0n
  }
  const [, second = grow(), third] = list
  return second === 0n ? third : -1n
}

/** A default in a loop's pattern runs before the names after it exist: reading `b` there throws. */
export function patternBeforeItsName(c: number) {
  const b = 100
  let total = 0
  for (const { f = () => b, a = f(), b } of [{ b: c }] as { f?: () => number; a?: number; b: number }[]) total += a + b
  return total
}

export function listPatternBeforeItsName(c: number) {
  const b = 100
  let total = 0
  const rows: [(() => number) | undefined, number | undefined, number | undefined][] = [[undefined, undefined, c]]
  for (const [f = () => b, a = f(), b] of rows) total += (a ?? 0) + (b ?? 0)
  return total
}

/** A default runs before the body, so a function declared in the body does not exist for it yet. */
export function defaultBeforeBody(c: number, a = () => inner()) {
  function inner() { return 1 }
  return a() + c
}
