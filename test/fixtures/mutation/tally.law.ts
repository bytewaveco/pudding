import { describe, domain, expect, law } from "@bytewaveco/pudding"
import {
  bump, deposit, depositIf, evens, KINDS, POWERS, pushThenChange, squares, sumUntilNegative, totals, visit, visitBySwitch, visitWhenDoubled,
  type Entry, type Kind,
} from "./tally.ts"

law("totals add each amount to the total of its kind", domain<[Entry, Entry]>(), ([a, b]) => {
  const result = totals([a, b])
  expect(result.assets + result.liabilities + result.equity).toEqual(a.amount + b.amount)
})

law("FALSE: totals put everything under assets", domain<[Entry, Entry]>(), ([a, b]) => {
  expect(totals([a, b]).assets).toEqual(a.amount + b.amount)
})

law("a change made by a function is seen by its caller", domain<[bigint, bigint]>(), ([start, amount]) => {
  const account = { balance: start }
  deposit(account, amount)
  expect(account.balance).toEqual(start + amount)
})

law("FALSE: a function cannot change what it is given", domain<[bigint, bigint]>(), ([start, amount]) => {
  const account = { balance: start }
  deposit(account, amount)
  expect(account.balance).toEqual(start)
})

law("two names for one object see the same change", domain<[bigint, bigint]>(), ([start, amount]) => {
  const account = { balance: start }
  const alias = account
  alias.balance += amount
  expect(account.balance).toEqual(start + amount)
})

law("FALSE: a second name is a separate object", domain<[bigint, bigint]>(), ([start, amount]) => {
  const account = { balance: start }
  const alias = account
  alias.balance += amount
  expect(account.balance).toEqual(start)
})

law("a copy is a separate object", domain<[bigint, bigint]>(), ([start, amount]) => {
  const account = { balance: start }
  const copy = { ...account }
  copy.balance += amount
  expect(account.balance).toEqual(start)
})

law("a change behind an early return happens only when the function gets there", domain<[bigint, bigint, boolean]>(), ([start, amount, really]) => {
  const account = { balance: start }
  const done = depositIf(account, amount, really)
  expect(account.balance).toEqual(really ? start + amount : start)
  expect(done).toEqual(really)
})

law("FALSE: a change behind an early return always happens", domain<[bigint, bigint, boolean]>(), ([start, amount, really]) => {
  const account = { balance: start }
  depositIf(account, amount, really)
  expect(account.balance).toEqual(start + amount)
})

law("a change in one branch of a condition is kept for that branch only", domain<[bigint, boolean]>(), ([start, flag]) => {
  const account = { balance: start }
  if (flag) account.balance += 1n
  else account.balance -= 1n
  expect(account.balance).toEqual(flag ? start + 1n : start - 1n)
})

law("an object inside an object is the same object wherever it is reached from", domain<bigint>(), amount => {
  const inner = { n: 0n }
  const outer = { inner, list: [inner] }
  outer.list[0]!.n += amount
  expect(inner.n).toEqual(amount)
  expect(outer.inner.n).toEqual(amount)
})

law("an array is built by pushing", () => {
  expect(squares()).toEqual([1, 4, 9, 16])
})

law("a push that depends on a counter is followed", () => {
  expect(evens(5)).toEqual([0, 2, 4])
})

law("REFUSED: changing an input in place", domain<{ balance: bigint }>(), account => {
  deposit(account, 1n)
  expect(account.balance).toEqual(account.balance)
})

law("positions of an array can be assigned", domain<[bigint, bigint]>(), ([a, b]) => {
  const pair = [a, b]
  const first = pair[0]!
  pair[0] = pair[1]!
  pair[1] = first
  expect(pair).toEqual([b, a])
})

law("REFUSED: changing a module constant", () => {
  const kinds = KINDS as Kind[]
  kinds.push("asset")
  expect(kinds.length).toEqual(4)
})

law("a constant may be built step by step while its module loads", () => {
  expect(POWERS).toEqual([1n, 2n, 4n, 8n, 16n])
})

law("REFUSED: a push on one side of a condition that is not known", domain<boolean>(), flag => {
  const out: bigint[] = []
  if (flag) out.push(1n)
  expect(out.length <= 1).toBe(true)
})

law("a push on both sides of a condition", domain<boolean>(), flag => {
  const out: bigint[] = []
  if (flag) out.push(1n)
  else out.push(2n)
  expect(out).toEqual([flag ? 1n : 2n])
})

law("REFUSED: an object that may be either of two is no longer changed", domain<[bigint, boolean]>(), ([start, flag]) => {
  const a = { n: start }
  const b = { n: 0n }
  const either = flag ? a : b
  a.n += 1n
  expect(either.n).toEqual(flag ? start + 1n : 0n)
})

law("a change through a value of two shapes lands on the one it is", domain<[bigint, boolean]>(), ([start, flag]) => {
  const a = { n: start }
  const b = { n: 0n, extra: true }
  const either = flag ? a : b
  either.n = 7n
  expect(a.n).toEqual(flag ? 7n : start)
  expect(b.n).toEqual(flag ? 0n : 7n)
})

law("a function keeps changing the object it closed over", () => {
  const counter = { n: 0n }
  const tick = () => {
    counter.n += 1n
  }
  tick()
  tick()
  expect(counter.n).toEqual(2n)
})

law("REFUSED: a change on the right of &&", domain<boolean>(), flag => {
  const counter = { n: 0n }
  const both = flag && bump(counter, 1n)
  expect(both).toEqual(flag)
})

law("REFUSED: a change inside a callback of some", domain<bigint>(), x => {
  const counter = { n: 0n }
  const found = [x, x + 1n].some(item => bump(counter, item))
  expect(found).toBe(true)
})

law("a callback of some may change what it creates itself", domain<bigint>(), x => {
  const found = [x, x + 1n].some(item => {
    const mine = { n: item }
    mine.n += 1n
    return mine.n > item
  })
  expect(found).toBe(true)
})

law("a callback of map runs for every element, changes and all", domain<[bigint, bigint]>(), ([x, y]) => {
  const seen = { sum: 0n }
  const doubled = [x, y].map(item => {
    seen.sum += item
    return item * 2n
  })
  expect(seen.sum).toEqual(x + y)
  expect(doubled).toEqual([x * 2n, y * 2n])
})

law("each side of a conditional expression makes its own change", domain<boolean>(), flag => {
  const counter = { n: 0n }
  const did = flag ? bump(counter, 1n) : bump(counter, -1n)
  expect(did).toBe(true)
  expect(counter.n).toEqual(flag ? 1n : -1n)
})

law("FALSE: both sides of a conditional expression change the object", domain<boolean>(), flag => {
  const counter = { n: 0n }
  const did = flag ? bump(counter, 1n) : bump(counter, -1n)
  expect(did).toBe(true)
  expect(counter.n).toEqual(0n)
})

law("a loop that stops early keeps the changes made before it stopped", domain<[bigint, bigint]>(), ([x, y]) => {
  const into = { sum: 0n }
  sumUntilNegative(into, [x, y])
  expect(into.sum).toEqual(x < 0n ? 0n : y < 0n ? x : x + y)
})

law("FALSE: a loop that stops early adds everything", domain<[bigint, bigint]>(), ([x, y]) => {
  const into = { sum: 0n }
  sumUntilNegative(into, [x, y])
  expect(into.sum).toEqual(x + y)
})

law("an object made and changed inside a branch keeps the change", domain<boolean>(), flag => {
  let result = { n: 5n }
  if (flag) {
    result = { n: 0n }
    result.n += 1n
  }
  expect(result.n).toEqual(flag ? 1n : 5n)
})

law("the old value is read before the right-hand side runs", () => {
  const counter = { n: 0n }
  const tenMore = () => {
    counter.n += 10n
    return 1n
  }
  counter.n += tenMore()
  expect(counter.n).toEqual(1n)
})

law("FALSE: the right-hand side's own change survives a compound assignment", () => {
  const counter = { n: 0n }
  const tenMore = () => {
    counter.n += 10n
    return 1n
  }
  counter.n += tenMore()
  expect(counter.n).toEqual(11n)
})

law("REFUSED: an object stored inside itself", () => {
  const node: { next: unknown; n: bigint } = { next: 0n, n: 1n }
  node.next = node
  expect(node.n).toEqual(1n)
})

law("a reducer may push to the list it carries", domain<[bigint, bigint]>(), ([x, y]) => {
  const doubled = [x, y].reduce((list, item) => {
    list.push(item * 2n)
    return list
  }, [] as bigint[])
  expect(doubled).toEqual([x * 2n, y * 2n])
})

law("a copy of a list is a separate list, holding the same objects", domain<bigint>(), x => {
  const item = { n: x }
  const list = [item]
  const copy = [...list]
  copy.push({ n: 0n })
  copy[0]!.n += 1n
  expect(list.length).toEqual(1)
  expect(item.n).toEqual(x + 1n)
})

law("a counter field can be stepped with ++", () => {
  const counter = { n: 0 }
  counter.n++
  counter.n++
  expect(counter.n).toEqual(2)
})

law("REFUSED: adding a property", () => {
  const bag: { a: bigint; b?: bigint } = { a: 1n }
  bag.b = 2n
  expect(bag.a).toEqual(1n)
})

law("a change at a key that is an input lands on that key only", domain<[Kind, bigint]>(), ([kind, amount]) => {
  const sums = { asset: 0n, liability: 0n, equity: 0n }
  sums[kind] += amount
  sums[kind] += amount
  expect(sums.asset).toEqual(kind === "asset" ? amount * 2n : 0n)
  expect(sums.asset + sums.liability + sums.equity).toEqual(amount * 2n)
})

law("FALSE: a change at a key that is an input lands on every key", domain<[Kind, bigint]>(), ([kind, amount]) => {
  const sums = { asset: 0n, liability: 0n, equity: 0n }
  sums[kind] += amount
  expect(sums.asset).toEqual(amount)
})

law("a key that may name no property has to be ruled out", domain<["asset" | "other", bigint]>(), ([kind, amount]) => {
  const sums = { asset: 0n, liability: 0n }
  if (kind === "asset") sums[kind] += amount
  expect(sums.asset).toEqual(kind === "asset" ? amount : 0n)
})

law("FALSE: a key that names no property", domain<["asset" | "other", bigint]>(), ([kind, amount]) => {
  const sums: Record<string, bigint> = { asset: 0n, liability: 0n }
  sums[kind]! += amount
  expect(sums["asset"]).toEqual(kind === "asset" ? amount : 0n)
})

// An object stored somewhere and then changed, both behind one condition.
// These were once proved with the count from before the change: the object
// was copied into the place it was stored before its own change was merged.
law("an object stored and then changed is seen changed from where it was stored", domain<boolean>(), go => {
  const node = { seen: 0n }
  const cursor = { node: { seen: 5n } }
  expect(visit(cursor, node, go)).toEqual(go ? 1n : 5n)
  expect(cursor.node.seen).toEqual(go ? 1n : 5n)
  expect(node.seen).toEqual(go ? 1n : 0n)
})

law("FALSE: an object stored and then changed keeps its old value where it was stored", domain<boolean>(), go => {
  const node = { seen: 0n }
  const cursor = { node: { seen: 5n } }
  expect(visit(cursor, node, go)).toEqual(go ? 0n : 5n)
})

law("an object stored and then changed, behind a condition no sample reaches", domain<[string, string]>(), ([s, t]) => {
  const node = { seen: 0n }
  const cursor = { node: { seen: 5n } }
  expect(visitWhenDoubled(cursor, node, s, t)).toEqual(s === t + t && t !== "" ? 1n : 5n)
})

law("FALSE: behind a condition no sample reaches, the old value is kept", domain<[string, string]>(), ([s, t]) => {
  const node = { seen: 0n }
  const cursor = { node: { seen: 5n } }
  expect(visitWhenDoubled(cursor, node, s, t)).toEqual(s === t + t && t !== "" ? 0n : 5n)
})

law("an object stored and then changed inside a switch", domain<"move" | "keep">(), step => {
  const node = { seen: 0n }
  const cursor = { node: { seen: 5n } }
  expect(visitBySwitch(step, cursor, node)).toEqual(step === "move" ? 1n : 5n)
  expect(cursor.node.seen).toEqual(step === "move" ? 1n : 5n)
})

law("FALSE: after a switch the caller sees the old value", domain<"move" | "keep">(), step => {
  const node = { seen: 0n }
  const cursor = { node: { seen: 5n } }
  visitBySwitch(step, cursor, node)
  expect(cursor.node.seen).toEqual(step === "move" ? 0n : 5n)
})

law("an object pushed and then changed is seen changed in the list", domain<boolean>(), flag => {
  expect(pushThenChange(flag)).toEqual(flag ? 1n : 2n)
})

law("FALSE: an object pushed and then changed keeps its old value in the list", domain<boolean>(), flag => {
  expect(pushThenChange(flag)).toEqual(0n)
})

law("what a variable holds after a condition is the object as the taken side left it", domain<boolean>(), go => {
  const node = { seen: 0n }
  let current = { seen: 5n }
  if (go) {
    current = node
    node.seen += 1n
  }
  expect(current.seen).toEqual(go ? 1n : 5n)
})

// What a group declares is shared by its laws, so a law that changed it would change what the next law sees.
describe("an object shared by the laws of a group", () => {
  const shared = { n: 0n }

  law("can be read", () => {
    expect(shared.n).toEqual(0n)
  })
})

describe("another object shared by the laws of a group", () => {
  const shared = { n: 0n }

  law("REFUSED: cannot be changed by one of them", () => {
    shared.n += 1n
    expect(shared.n).toEqual(1n)
  })
})
