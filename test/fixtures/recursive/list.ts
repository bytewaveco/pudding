export type Node = { v: 1 | 2; next?: Node }
export function depth(n: Node | undefined): number { return n === undefined ? 0 : 1 }
export const table = new Map([["a", 1]])
export function viaTable(k: string) { return table.get(k) }
