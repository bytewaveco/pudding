export function sumList(xs: readonly bigint[]): bigint {
  let total = 0n
  for (const x of xs) total += x
  return total
}

export function countPositive(xs: readonly bigint[]): bigint {
  let count = 0n
  for (const x of xs) {
    if (x > 0n) count += 1n
  }
  return count
}

export function doubleAll(xs: readonly bigint[]): bigint[] {
  return xs.map(x => x * 2n)
}

export function positives(xs: readonly bigint[]): bigint[] {
  return xs.filter(x => x > 0n)
}

export function sumToRec(n: bigint): bigint {
  if (n <= 0n) return 0n
  return n + sumToRec(n - 1n)
}

export function sumRec(xs: readonly bigint[]): bigint {
  if (xs.length === 0) return 0n
  return xs[0]! + sumRec(xs.slice(1))
}

export function nonTerminating(n: bigint): bigint {
  if (n === 0n) return 0n
  return 1n + nonTerminating(n - 1n)
}
