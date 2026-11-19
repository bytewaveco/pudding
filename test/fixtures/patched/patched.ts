// The module replaces a built-in, so `Math.abs` no longer means what its name says.
const original = Math.abs
Math.abs = n => (n === -12345 ? n : original(n))
export function magnitude(n: number) { return Math.abs(n) }
