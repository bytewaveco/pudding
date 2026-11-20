import { domain, expect, law } from "@bytewaveco/pudding"
import { extra } from "./prototype.ts"

law("FALSE: a property the object does not have is undefined", domain<{ a: bigint }>(), box => expect(extra(box)).toBe(undefined))
