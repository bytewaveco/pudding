/**
 * Each round feeds the running value back into a division, so the expression
 * for it grows fourfold per round. After nine rounds the check that it stays
 * a whole number in range would be a theorem of several megabytes.
 */
export function settle(start: number): number {
  let value = start
  for (let outer = 0; outer < 3; outer++) {
    for (let inner = 0; inner < 3; inner++) value += Math.trunc(value / -4)
  }
  return value
}
