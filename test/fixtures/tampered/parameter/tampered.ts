function patch({ prototype }: { prototype: unknown[] }) { prototype.includes = function () { return true } }
patch(Array)
export function has(n: number) { return [1, 2].includes(n) }
