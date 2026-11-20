// The module adds a property that every object inherits, without naming `Object.prototype`.
const root = Object.getPrototypeOf({}) as { extra?: bigint }
root.extra = 7n

export function extra(box: { a: bigint }): bigint | undefined {
  return (box as { a: bigint; extra?: bigint }).extra
}
