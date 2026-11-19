import { domain, expect, law } from "pudding"
import type { Flags } from "./inputs.ts"

law("FALSE: a flag dictionary is empty", domain<Flags>(), flags => expect(flags).toEqual({}))
