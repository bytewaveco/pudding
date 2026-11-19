// The module replaces how arrays are iterated, so `for...of` no longer visits every element.
const original = Array.prototype[Symbol.iterator]
Array.prototype[Symbol.iterator] = function* <T>(this: T[]) {
  let first = true
  for (const value of original.call(this) as IterableIterator<T>) {
    if (first) yield value
    first = false
  }
} as typeof original

export function sum(values: readonly bigint[]): bigint {
  let total = 0n
  for (const value of values) total += value
  return total
}
