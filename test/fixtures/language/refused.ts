export function makeCounter(start: bigint): bigint {
  let count = start
  const increment = () => {
    count += 1n
    return count
  }
  increment()
  return count
}

function counterFrom(start: bigint) {
  let count = start
  return () => {
    count += 1n
    return count
  }
}

export function countsLater(start: bigint): bigint {
  const next = counterFrom(start)
  next()
  return next()
}

export function readsLater(flag: boolean): bigint {
  let value = 1n
  const read = () => value
  if (flag) value = 2n
  return read()
}

export function mutatesObject(amount: bigint): bigint {
  const totals = { sum: 0n }
  totals.sum += amount
  return totals.sum
}

export function pushes(amount: bigint): bigint {
  const items: bigint[] = []
  items.push(amount)
  return items[0]!
}

export function chained(amount: bigint): bigint {
  let a = 0n
  let b = 0n
  a = b = amount
  return a + b
}

export function whileLoop(limit: 1n | 2n | 3n): bigint {
  let i = 0n
  while (i < limit) i += 1n
  return i
}
