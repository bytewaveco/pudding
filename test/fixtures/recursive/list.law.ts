import { domain, expect, law } from "@bytewaveco/pudding"
import { depth, type Node } from "./list.ts"
law("recursive type", domain<Node>(), n => { expect(depth(n)).toBe(1) })
law("an ordinary law in the same file", () => { expect(depth(undefined)).toBe(0) })
