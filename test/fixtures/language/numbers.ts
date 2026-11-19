export function pageCount(total: number, pageSize: number): number {
  return Math.ceil(total / pageSize)
}

export function pageOf(index: number, pageSize: number): number {
  return Math.floor(index / pageSize)
}

export function clampPercent(value: number): number {
  return Math.min(100, Math.max(0, value))
}

export function sumTo(limit: number): number {
  let sum = 0
  for (let i = 1; i <= limit; i++) sum += i
  return sum
}

export function sumIndexed(values: readonly number[]): number {
  let sum = 0
  for (let i = 0; i < values.length; i++) sum += values[i]!
  return sum
}

export function countdown(from: number): number {
  let steps = 0
  let left = from
  while (left > 0) {
    left -= 1
    steps++
  }
  return steps
}

export function minutes(hours: number, extra: number): number {
  return hours * 60 + extra
}

export function parity(value: number): "even" | "odd" {
  return value % 2 === 0 ? "even" : "odd"
}

export function label(count: number): string {
  return `${count} item${count === 1 ? "" : "s"}`
}

export function toCents(dollars: bigint): number {
  return Number(dollars * 100n)
}

export function average(a: number, b: number): number {
  return (a + b) / 2
}
