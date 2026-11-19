import { expect, law } from "pudding"
import { subject } from "./subject.ts"

law("FALSE: the module loads", () => expect(subject()).toBe(true))
