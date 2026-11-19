import { expect, law } from "@bytewaveco/pudding"
import { subject } from "./subject.js"

law("FALSE: the TypeScript file is the one that runs", () => expect(subject()).toBe(true))
