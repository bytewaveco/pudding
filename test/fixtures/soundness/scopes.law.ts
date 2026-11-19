import { domain, expect, law } from "pudding"
import { defaultScope, emptyMap, ownName, varScope } from "./scopes.ts"

law("FALSE: the default reads the body's label", domain<bigint>(), id => expect(defaultScope(id)).toBe("closed"))
law("FALSE: the outer flag is the one read", domain<bigint>(), n => expect(varScope(n)).toBe(true))
law("FALSE: the name refers to the outer function", () => expect(ownName()).toBe(false))
law("FALSE: mapping nothing needs no function", () => expect(emptyMap()).toEqual([]))
