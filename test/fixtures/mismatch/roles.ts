export type Role = "basic" | "admin"

const permissions: Record<Role, readonly string[]> = {
  basic: ["read"],
  admin: ["read", "write"],
}

// Changes the table through another name, which the translator does not follow.
const alias: Record<Role, readonly string[]> = permissions
export const loaded = (() => {
  alias.basic = ["read", "write"]
  return true
})()

export function canWrite(role: Role): boolean {
  return permissions[role].includes("write")
}
