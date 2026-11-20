/**
 * Each round feeds the running value back into a division. Without DAG sharing
 * (`let`-CSE), nine rounds would expand to 33 MB; with `let`-CSE, nine rounds
 * stay small and are proved.
 */
export function settle(start: number): number {
  let value = start
  for (let outer = 0; outer < 3; outer++) {
    for (let inner = 0; inner < 3; inner++) value += Math.trunc(value / -4)
  }
  return value
}

/**
 * A loop with hundreds of distinct steps still builds an expression past
 * Lean's text size limit, which is refused quickly instead of hanging Lean.
 */
export function huge(start: bigint): bigint {
  let value = start
  for (let i = 1; i <= 1500; i++) {
    const k = BigInt(i)
    value = value + (value < k ? k : k + 1n) + (value < k + 10n ? k + 2n : k + 3n)
  }
  return value
}
