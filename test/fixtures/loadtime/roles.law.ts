import { domain, expect, law } from "@bytewaveco/pudding"
import { canWrite, type Role } from "./roles.ts"

law("everyone writes once the table is patched", domain<Role>(), role => {
  expect(canWrite(role)).toBe(true)
})
