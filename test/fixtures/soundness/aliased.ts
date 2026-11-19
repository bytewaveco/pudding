// `write` is Object.assign under another name; `as const` does not stop it.
const table = { ok: false } as const
const write = Object.assign
const set = write(table, { ok: true })
export const whileSet = table.ok
const reset = write(table, { ok: false })
export const unused = [set, reset]
