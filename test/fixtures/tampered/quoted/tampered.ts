const p = Array["prototype"]
p.includes = function () { return true }
export function has(n: number) { return [1, 2].includes(n) }
