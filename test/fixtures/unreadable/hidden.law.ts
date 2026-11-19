import { expect, law } from "pudding"

// A law registered from inside a statement is never read as a law.
if (true) law("FALSE: hidden in a condition", () => expect(false).toBe(true))
