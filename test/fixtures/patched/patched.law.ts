import { domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { magnitude } from "./patched.ts"

law("FALSE: a magnitude is never negative", domain<Integer>(), n => expect(magnitude(n) >= 0).toBe(true))
