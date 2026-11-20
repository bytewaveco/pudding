export function total(amounts: readonly bigint[]): bigint {
  return amounts.concat().reduce((sum, amount) => sum + amount, 0n)
}

export function initials(name: "ada" | "grace"): string {
  return name.slice(0, 1).toUpperCase()
}
