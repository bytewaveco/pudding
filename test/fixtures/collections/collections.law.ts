import { domain, expect, law } from "@bytewaveco/pudding"
import { known, price } from "./collections.ts"

law("FALSE: a Map gives what was put into it", domain<"a" | "b">(), key => expect(price(key)).toBe(key === "a" ? 1n : undefined))
law("FALSE: a Set only has what was added", domain<bigint>(), value => expect(known(value)).toBe(value === 1n))
