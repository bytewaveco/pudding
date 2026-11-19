import { domain, expect, law } from "@bytewaveco/pudding"
import { next, type Light } from "./lights.ts"

law.only("the one law that runs", domain<Light>(), light => {
  expect(next(light)).not.toEqual(light)
})

law("FALSE but not selected: red is terminal", () => {
  expect(next("red")).toEqual("red")
})
