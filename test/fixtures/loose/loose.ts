export function orZero(value: bigint | undefined): bigint {
  return value === undefined ? 0n : value
}
