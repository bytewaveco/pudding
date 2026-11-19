import { domain, expect, law } from "pudding"
import {
  defaultOnUndefined, forInitializer, loopHeader, mixedIncludes, mixedSwitch, ownExpect, parameterScope, readAcrossBranches, shorthandRead,
  switchScope, unsetLet,
} from "./state.ts"

law("FALSE: an unset let is always assigned", domain<bigint>(), n => expect(unsetLet(n)).toBe(true))
law("FALSE: the default never runs", domain<bigint>(), n => expect(defaultOnUndefined(n)).toBe(true))
law("FALSE: the later declaration is always readable", domain<bigint>(), n => expect(readAcrossBranches(n)).toBe(true))
law("FALSE: a shorthand property reads nothing", domain<bigint>(), n => expect(shorthandRead(n)).toBe(true))
law("FALSE: a number in a list matches a bigint", domain<bigint>(), n => expect(mixedIncludes(n)).toBe(n === 424242n))
law("FALSE: a number case matches a bigint", domain<bigint>(), n => expect(mixedSwitch(n)).toBe(n === 424242n))
law("FALSE: the local expect is the library's", domain<bigint>(), n => expect(ownExpect(n)).toBe(true))
law("FALSE: the case label calls the parameter", () => expect(switchScope(() => true)).toBe(true))
law("FALSE: the iterable reads the outer item", () => expect(loopHeader()).toBe(true))
law("FALSE: the first initializer reads the outer flag", () => expect(forInitializer()).toBe(true))
law("FALSE: the first default reads the outer flag", () => expect(parameterScope()).toBe(true))

// An unfinished proof is not a proof, whatever Lean's exit status.
law("FALSE: every bigint is zero", domain<bigint>(), n => expect(n).toBe(0n), { proof: "sorry" })
law("FALSE: every bigint survives a round trip through number", domain<bigint>(), n => expect(BigInt(Number(n))).toBe(n), { proof: "sorry" })
