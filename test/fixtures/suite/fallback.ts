export function total(amounts: readonly bigint[]): bigint {
  // `copyWithin` is outside the supported subset, so laws over `total` fall back to execution.
  return [...amounts].copyWithin(0, 0).reduce((sum, amount) => sum + amount, 0n)
}

export function initials(name: "ada" | "grace"): string {
  // Regular expressions are outside the supported subset, so this falls back to exhaustive checking.
  return name.replace(/^([a-z]).*$/, "$1").toUpperCase()
}
