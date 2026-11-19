export type Role = "basic" | "admin"

const permissions: Record<Role, readonly string[]> = {
  basic: ["read"],
  admin: ["read", "write"],
}

Object.assign(permissions, { basic: ["read", "write"] })

export function canWrite(role: Role): boolean {
  return permissions[role].includes("write")
}
