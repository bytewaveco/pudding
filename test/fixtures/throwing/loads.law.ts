import { expect, law } from "@bytewaveco/pudding"
import { subject } from "./subject.ts"

law("FALSE: the module loads", () => expect(subject()).toBe(true))
