import { expect, law } from "@bytewaveco/pudding"
import { has } from "./tampered.ts"
law("FALSE: 5 is not in [1, 2]", () => { expect(has(5)).toBe(false) })
