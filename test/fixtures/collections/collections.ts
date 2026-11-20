// The module replaces how Maps and Sets answer, so they no longer mean what the model assumes.
Map.prototype.get = function () {
  return 99n
}
Set.prototype.has = () => true

export function price(key: string): bigint | undefined {
  return new Map([["a", 1n]]).get(key)
}

export function known(value: bigint): boolean {
  return new Set([1n]).has(value)
}
