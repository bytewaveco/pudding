import { domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { clock, column, decimal, trailing } from "./format.ts"

law("a negative amount is the positive amount with a minus sign", domain<Integer<1, 200>>(), cents => {
  expect(decimal(BigInt(-cents))).toEqual("-" + decimal(BigInt(cents)))
})

law("amounts under a dollar keep their leading zero", domain<Integer<0, 99>>(), cents => {
  expect(decimal(BigInt(cents))).toEqual(cents < 10 ? `0.0${cents}` : `0.${cents}`)
})

law("known amounts", () => {
  expect(decimal(5n)).toEqual("0.05")
  expect(decimal(-1205n)).toEqual("-12.05")
  expect(decimal(100n)).toEqual("1.00")
  expect(decimal(0n)).toEqual("0.00")
})

law("FALSE: single cents are written without a zero", domain<Integer<0, 9>>(), cents => {
  expect(decimal(BigInt(cents))).toEqual(`0.${cents}`)
})

law("a clock always has two digits each side", domain<[Integer<0, 23>, Integer<0, 59>]>(), ([hours, minutes]) => {
  expect(clock(hours, minutes)).toEqual(`${hours < 10 ? "0" : ""}${hours}:${minutes < 10 ? "0" : ""}${minutes}`)
})

law("FALSE: a clock pads with spaces", domain<[Integer<0, 23>, Integer<0, 59>]>(), ([hours, minutes]) => {
  expect(clock(hours, minutes)).toEqual(`${hours < 10 ? " " : ""}${hours}:${minutes < 10 ? "0" : ""}${minutes}`)
})

law("padding repeats and cuts its filler, and counts the minus sign", domain<-150n | -15n | -5n | 0n | 7n | 42n | 123n | 4567n | 98765n>(), value => {
  expect(column(value)).toEqual(
    value === -150n ? "-150" : value === -15n ? "a-15" : value === -5n ? "ab-5" : value === 0n ? "aba0" : value === 7n ? "aba7"
      : value === 42n ? "ab42" : value === 123n ? "a123" : value === 4567n ? "4567" : "98765",
  )
})

law("padding at the end", domain<-15n | -5n | 0n | 42n | 123n | 4567n>(), value => {
  expect(trailing(value)).toEqual(
    value === -15n ? "-15" : value === -5n ? "-5." : value === 0n ? "0.." : value === 42n ? "42." : value === 123n ? "123" : "4567",
  )
})

law("padding an arbitrary symbolic string is idempotent and enforces minimum UTF-16 length", domain<string>(), text => {
  const padded = text.padStart(4, "0")
  expect(padded.padStart(4, "0")).toEqual(padded)
  expect(padded.length >= 4).toBe(true)
  expect(padded.endsWith(text)).toBe(true)
  expect(text.padEnd(4, " ").startsWith(text)).toBe(true)
  expect("😀".length).toEqual(2)
  expect("😀".padStart(3, "0")).toEqual("0😀")
})

law("symbolic string length, affixes and boundary slices hold for all Unicode text", domain<[string, string]>(), ([a, b]) => {
  expect(a.length >= 0).toBe(true)
  expect((a.length === 0) === (a === "")).toBe(true)
  expect(a.length <= (a + b).length).toBe(true)
  expect((a + b).startsWith(a)).toBe(true)
  expect((a + b).endsWith(b)).toBe(true)
  expect((a + b).includes(a)).toBe(true)
  expect((a + b).includes(b)).toBe(true)
  if (a.startsWith(b)) {
    expect(b.length <= a.length).toBe(true)
    expect(a.includes(b)).toBe(true)
  }
  expect(("pre_" + a).slice(4)).toEqual(a)
  expect(("USD:" + a).slice(0, 3)).toEqual("USD")
  expect((a + ".ts").slice(0, -3)).toEqual(a)
  expect((a + ".ts").slice(-3)).toEqual(".ts")
})

law("FALSE: every one-code-point string has UTF-16 length 1", domain<string>(), text => {
  if (text.startsWith("😀")) expect(text.length).toEqual(1)
})

law("FALSE: startsWith implies equal length", domain<[string, string]>(), ([a, b]) => {
  if (a.startsWith(b)) expect(a.length).toEqual(b.length)
})

law("REFUSED: padding with a non-BMP multi-unit character", domain<string>(), text => {
  expect(text.padStart(4, "😀").length >= 4).toBe(true)
})

law("REFUSED: slicing an arbitrary symbolic string at a mid-string offset", domain<string>(), text => {
  expect(text.slice(1).length <= text.length).toBe(true)
})
