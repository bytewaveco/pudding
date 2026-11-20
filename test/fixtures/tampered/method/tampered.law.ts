import { expect, law } from "@bytewaveco/pudding"
import { first } from "./tampered.ts"
law("FALSE: an empty list has no first element", () => { expect(first([])).toBe(undefined) })
