export function total(amounts: readonly bigint[]): bigint {
  let sum = 0n
  for (const amount of amounts) sum += amount
  return sum
}

export function largest(values: readonly bigint[]): bigint {
  let best = values[0]!
  for (const value of values) {
    if (value > best) best = value
  }
  return best
}

export function countPositive(values: readonly bigint[]): bigint {
  let count = 0n
  for (const value of values) {
    if (value <= 0n) continue
    count++
  }
  return count
}

export function firstNegative(values: readonly bigint[]): bigint {
  let found = 0n
  for (const value of values) {
    if (value < 0n) {
      found = value
      break
    }
  }
  return found
}

export function indexOfZero(values: readonly bigint[]): bigint {
  let index = 0n
  for (const value of values) {
    if (value === 0n) return index
    index += 1n
  }
  return -1n
}

export type Tier = "bronze" | "silver" | "gold"

export function discount(tier: Tier, amount: bigint, loyal: boolean): bigint {
  let rate = 0n
  if (tier === "silver") rate = 5n
  else if (tier === "gold") rate = 10n
  if (loyal) rate += 2n
  let result = amount
  result -= (amount * rate) / 100n
  return result
}

export function describeTier(tier: Tier): string {
  let text = "tier"
  switch (tier) {
    case "gold":
      text += ":gold"
      break
    case "silver":
      text += ":silver"
      break
    default:
      text += ":bronze"
  }
  return text
}

export function bump(value: bigint, times: Tier): bigint {
  // Parameters are reassignable.
  if (times === "gold") value = value + 2n
  if (times !== "bronze") value++
  value--
  return value
}

export interface Line {
  debit: bigint
  credit: bigint
}

export function journalTotals(lines: readonly Line[]) {
  return lines.reduce(
    (result, line) => ({ debits: result.debits + line.debit, credits: result.credits + line.credit }),
    { debits: 0n, credits: 0n },
  )
}

export function cents(value: bigint): string {
  const absolute = value < 0n ? -value : value
  return `${value < 0n ? "-" : ""}${absolute / 100n}.${String(absolute % 100n)}c`
}

export function signed(value: bigint): string {
  return value.toString() + "!" + String(value)
}

export function assertPositive(value: bigint): void {
  if (value <= 0n) throw new Error("must be positive")
}
