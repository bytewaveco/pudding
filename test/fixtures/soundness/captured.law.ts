import { expect, law } from "@bytewaveco/pudding"
import { readViaAlias, readViaHelper, readViaMethod } from "./captured.ts"

law("FALSE: a table aliased through ?? keeps its value", () => expect<boolean>(readViaAlias).toBe(false))
law("FALSE: a table's own method changes nothing", () => expect(readViaMethod).toBe(false))
law("FALSE: a project function leaves an as-const table alone", () => expect<boolean>(readViaHelper).toBe(false))
