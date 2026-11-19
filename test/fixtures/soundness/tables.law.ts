import { expect, law } from "@bytewaveco/pudding"
import { whileSet as throughAlias } from "./aliased.ts"
import { whileSet as throughCopy } from "./copied.ts"

law("FALSE: a value read during a temporary change through a copy is the initial one", () => expect(throughCopy).toBe(false))
law("FALSE: a value read during a temporary change through an alias is the initial one", () => expect(throughAlias).toBe(false))
