/** Whole cents as a decimal amount, such as `-12.05`. */
export function decimal(cents: bigint): string {
  const absolute = cents < 0n ? -cents : cents
  return `${cents < 0n ? "-" : ""}${absolute / 100n}.${String(absolute % 100n).padStart(2, "0")}`
}

export function clock(hours: number, minutes: number): string {
  return `${String(hours).padStart(2, "0")}:${String(minutes).padStart(2, "0")}`
}

export function column(value: bigint): string {
  return String(value).padStart(4, "ab")
}

export function trailing(value: bigint): string {
  return String(value).padEnd(3, ".")
}
