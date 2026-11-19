import { domain, expect, law } from "pudding"
import "./patch.ts"
import { canWrite, type Role } from "./roles.ts"

law("only admins write", domain<Role>(), role => {
  expect(canWrite(role)).toEqual(role === "admin")
})
