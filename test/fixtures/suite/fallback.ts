export function total(amounts: readonly bigint[]): bigint {
  let sum = 0n
  for (const amount of amounts) sum += amount
  return sum
}

export function initials(name: "ada" | "grace"): string {
  return name.slice(0, 1).toUpperCase()
}
