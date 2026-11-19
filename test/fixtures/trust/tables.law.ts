import { expect, law } from "@bytewaveco/pudding"
import { commentCode, fieldCode, fixedCode, innerCode, outerCode, wrappedCode } from "./tables.ts"

law("a table that is `as const` as a whole keeps its code", () => {
  expect(fixedCode()).toEqual("usd")
})

law("FALSE: one field `as const` protects the table", () => {
  expect(fieldCode()).toEqual("usd")
})

law("FALSE: a comment that says as const protects the table", () => {
  expect(commentCode()).toEqual("usd")
})

law("FALSE: parentheses protect the table", () => {
  expect(wrappedCode()).toEqual("usd")
})

law("FALSE: a table referred to from an `as const` table is protected", () => {
  expect(innerCode()).toEqual("usd")
})

law("FALSE: an `as const` table protects what it refers to", () => {
  expect(outerCode()).toEqual("usd")
})
