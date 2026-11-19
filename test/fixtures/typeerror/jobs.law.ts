import { expect, law } from "@bytewaveco/pudding"
import { cancel } from "./jobs.ts"

law("a state that does not exist", () => {
  expect(cancel("bogus")).toEqual("queued")
})
