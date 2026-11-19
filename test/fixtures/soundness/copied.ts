// A spread copies one level only, so `copy.row` is the table's own row.
const table = { row: { ok: false } }
const copy = { ...table }
const set = copy.row.ok = true
export const whileSet = table.row.ok
const reset = copy.row.ok = false
export const unused = [set, reset]
