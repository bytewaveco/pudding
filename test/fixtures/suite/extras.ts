export type Level = "low" | "mid" | "high" | "max"
export type Bit = 0n | 1n

export const levels = ["low", "mid", "high", "max"] as const satisfies readonly Level[]

const weights = { low: 1n, mid: 2n, high: 4n, max: 4n } as const

export function weight(level: Level): bigint {
  return weights[level]
}

export function rank(level: Level): bigint {
  switch (level) {
    case "low":
      return 0n
    case "mid":
      return 1n
    case "high":
    case "max":
      return 2n
  }
}

export function bump(level: Level, by = 1n): bigint {
  const base = rank(level)
  function capped(value: bigint) {
    return value > 2n ? 2n : value
  }
  if (by < 0n) {
    return base
  } else {
    return capped(base + by)
  }
}

export const describeLevel = (level: Level, quote: string) => quote + `level:${level}` + quote

export function xor(a: Bit, b: Bit): Bit {
  return a === b ? 0n : 1n
}

export interface Account {
  owner: { name: string; admin: boolean }
  balance: bigint
}

export function deposit(account: Account, amount: bigint): Account {
  if (amount <= 0n) throw new Error("deposits must be positive")
  return { ...account, balance: account.balance + amount }
}

export const greeting = (name: 'ü' | 'a"b' | "back\\slash" | "😀" | "tab\there") => `<${name}>`
