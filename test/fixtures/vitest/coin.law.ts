import { domain, expect, law } from "@bytewaveco/pudding"

type Side = "heads" | "tails"
const flip = (side: Side): Side => (side === "heads" ? "tails" : "heads")

// A second file, because Vitest proves files side by side.
law("flipping twice gives the side back", domain<Side>(), side => {
  expect(flip(flip(side))).toEqual(side)
})
