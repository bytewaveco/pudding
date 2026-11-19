import { expect, law } from "@bytewaveco/pudding"
import { ready } from "./loading.ts"

law("FALSE: ready initializes to true", () => expect(ready).toBe(true))
