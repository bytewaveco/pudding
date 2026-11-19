import { domain, expect, law } from "@bytewaveco/pudding"
import { callbackIndex, castKey, deadZone, erasedThis, hoisted, protoLiteral, tableWrite } from "./scoping.ts"

law("FALSE: the outer function supplies the result", () => expect(hoisted()).toBe(true))
law("FALSE: reading the binding succeeds", () => expect(deadZone()).toBe(true))
law("FALSE: the erased parameter takes the argument", () => expect(erasedThis(true)).toBe(false))
law("FALSE: the callback uses its default index", () => expect(callbackIndex()).toBe(true))
law("FALSE: every flag is set", domain<string>(), key => expect(castKey(key)).toBe(true))
law("FALSE: the literal stores its tag", () => expect(protoLiteral()).toBe("metadata"))
law("FALSE: the initial flag survives configuration", () => expect(tableWrite()).toBe(false))
