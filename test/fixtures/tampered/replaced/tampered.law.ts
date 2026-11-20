import { expect, law } from "@bytewaveco/pudding"
import { lookup } from "./tampered.ts"
law("FALSE: a is found", () => { expect(lookup("a")).toBe(1) })
