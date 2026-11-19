import { domain, expect, law } from "@bytewaveco/pudding"
import type { Flags, Tagged } from "./inputs.ts"

law("FALSE: a flag dictionary is empty", domain<Flags>(), flags => expect(flags).toEqual({}))
law("FALSE: different tags are structurally unequal", domain<[Tagged<true>, Tagged<false>]>(), ([a, b]) => expect<object>(a).not.toEqual(b))
