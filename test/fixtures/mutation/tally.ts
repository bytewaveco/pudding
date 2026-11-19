export type Kind = "asset" | "liability" | "equity"

export interface Entry {
  kind: Kind
  amount: bigint
}

/** Adds each entry to its own total, changing the running totals in place. */
export function totals(entries: readonly Entry[]) {
  return entries.reduce(
    (result, entry) => {
      switch (entry.kind) {
        case "asset":
          result.assets += entry.amount
          break
        case "liability":
          result.liabilities += entry.amount
          break
        case "equity":
          result.equity += entry.amount
      }
      return result
    },
    { assets: 0n, liabilities: 0n, equity: 0n },
  )
}

/** Changes the object it is given, and returns nothing. */
export function deposit(account: { balance: bigint }, amount: bigint): void {
  account.balance += amount
}

/** Changes the object it is given only when asked to, and leaves early otherwise. */
export function depositIf(account: { balance: bigint }, amount: bigint, really: boolean): boolean {
  if (!really) return false
  account.balance += amount
  return true
}

export function evens(limit: number): number[] {
  const out: number[] = []
  for (let n = 0; n < limit; n++) {
    if (n % 2 === 0) out.push(n)
  }
  return out
}

export function squares(): number[] {
  const out: number[] = []
  for (let n = 1; n <= 4; n++) out.push(n * n)
  return out
}

/** Changes the object it is given, and says so. */
export function bump(counter: { n: bigint }, by: bigint): boolean {
  counter.n += by
  return true
}

/** Adds the items up into `into`, stopping at the first negative one. */
export function sumUntilNegative(into: { sum: bigint }, items: readonly bigint[]): void {
  for (const item of items) {
    if (item < 0n) break
    into.sum += item
  }
}

export const KINDS: readonly Kind[] = ["asset", "liability", "equity"]

/** Built step by step while its module loads. */
export const POWERS: readonly bigint[] = (() => {
  const out: bigint[] = [1n]
  for (let n = 0; n < 4; n++) out.push(out[n]! * 2n)
  return out
})()

export interface Node {
  seen: bigint
}

/** Points the cursor at `node` and then counts the visit on it, when asked to. */
export function visit(cursor: { node: Node }, node: Node, go: boolean): bigint {
  if (go) {
    cursor.node = node
    node.seen += 1n
  }
  return cursor.node.seen
}

/** The same two steps, taken only when `s` is `t` written twice. */
export function visitWhenDoubled(cursor: { node: Node }, node: Node, s: string, t: string): bigint {
  if (s === t + t && t !== "") {
    cursor.node = node
    node.seen += 1n
  }
  return cursor.node.seen
}

/** The same two steps inside a switch that is left with `break`. */
export function visitBySwitch(step: "move" | "keep", cursor: { node: Node }, node: Node): bigint {
  switch (step) {
    case "move":
      cursor.node = node
      node.seen += 1n
      break
    case "keep":
      break
  }
  return cursor.node.seen
}

/** Puts a different object in the list on each side, and changes it after putting it there. */
export function pushThenChange(flag: boolean): bigint {
  const a = { n: 0n }
  const b = { n: 0n }
  const list: { n: bigint }[] = []
  if (flag) {
    list.push(a)
    a.n = 1n
  } else {
    list.push(b)
    b.n = 2n
  }
  return list[0]!.n
}
