import { describe, domain, expect, law } from "pudding"
import { next, type Light } from "./lights.ts"

law("three steps return to the start", domain<Light>(), light => {
  expect(next(next(next(light)))).toEqual(light)
})

describe("a single step", () => {
  const stops = (light: Light) => next(light) === "red"

  law("always changes the light", domain<Light>(), light => {
    expect(next(light)).not.toEqual(light)
  })

  law("stops only after amber", domain<Light>(), light => {
    expect(stops(light)).toEqual(light === "amber")
  })

  describe("from red", () => {
    law("goes to green", () => {
      expect(next("red")).toEqual("green")
    })
  })

  law.skip("FALSE but skipped: never reaches amber", domain<Light>(), light => {
    expect(next(light)).not.toEqual("amber")
  })

  law.todo("flashing amber")
})

describe.skip("a group that is switched off", () => {
  law("FALSE but skipped: red is green", () => {
    expect(next("red")).toEqual("red")
  })
})
