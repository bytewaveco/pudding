export function clamp(x: bigint, lo: bigint, hi: bigint): bigint {
  if (x < lo) return lo
  if (x > hi) return hi
  return x
}

export function abs(x: bigint) {
  return x < 0n ? -x : x
}

export function applyBasisPoints(amount: bigint, bps: bigint): bigint {
  return (amount * bps) / 10_000n
}

export function perPart(total: bigint, parts: bigint): bigint {
  return total / parts
}

export function roundToDollars(cents: bigint): bigint {
  const half = cents < 0n ? -50n : 50n
  return (cents + half) / 100n
}
