import { describe, domain, expect, law } from "@bytewaveco/pudding"
import { isEven, opposite, type Face } from "./dice.ts"

law("opposite faces add up to seven", domain<Face>(), face => {
  expect(opposite(face) + face).toEqual(7)
})

describe("parity", () => {
  law("opposite faces differ in parity", domain<Face>(), face => {
    expect(opposite(face) % 2 === 0).toEqual(!isEven(face))
  })

  law("FALSE: every face is even", domain<Face>(), face => {
    expect(isEven(face)).toBe(true)
  })

  law.skip("skipped: not checked", domain<Face>(), face => {
    expect(isEven(face)).toBe(false)
  })

  law.todo("a fair die")
})
