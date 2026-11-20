import { domain, expect, law } from "@bytewaveco/pudding"
import { extra } from "./tampered.ts"
law("FALSE: a box has no extra", domain<{ a: bigint }>(), box => { expect(extra(box)).toBe(undefined) })
