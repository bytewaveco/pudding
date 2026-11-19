export function total(amounts: readonly bigint[]): bigint {
  let sum = 0n
  for (let index = 0; index < amounts.length; index++) sum += amounts[index]!
  return sum
}

export function initials(name: "ada" | "grace"): string {
  return name.slice(0, 1).toUpperCase()
}
