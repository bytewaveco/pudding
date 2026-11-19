export type Role = "basic" | "admin"

export const permissions: Record<Role, readonly string[]> = {
  basic: ["read"],
  admin: ["read", "write"],
}

export function canWrite(role: Role): boolean {
  return permissions[role].includes("write")
}
