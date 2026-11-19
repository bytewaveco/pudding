import { keep, touch, touchInner } from "registry"

// The whole table is `as const`: an installed package may be given it.
const fixed = { usd: "usd" } as const satisfies { usd: string }
export const fixedEntry = keep(fixed)
export const fixedCode = (): string => fixed.usd

// Only one field is `as const`. The table itself can be changed.
const field = { usd: "usd" as string, kind: "fiat" as const } satisfies { usd: string; kind: string }
export const fieldEntry = touch(field)
export const fieldCode = (): string => field.usd

// The words appear in a comment and nowhere else.
const comment = {
  usd: "usd", // stored as const data
} satisfies { usd: string }
export const commentEntry = touch(comment)
export const commentCode = (): string => comment.usd

// Wrapped in parentheses, with no assertion at all.
const wrapped = ({ usd: "usd" })
export const wrappedEntry = touch(wrapped)
export const wrappedCode = (): string => wrapped.usd

// `as const` on the outer table does not reach a table it only refers to.
const inner = { usd: "usd" }
const outer = { inner } as const
export const outerEntry = touchInner(outer)
export const innerCode = (): string => inner.usd
export const outerCode = (): string => outer.inner.usd
