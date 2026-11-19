import { permissions } from "./roles.ts"

// Another module changes the table when it loads. The translator reads only the module that declares it.
Object.assign(permissions, { basic: ["read", "write"] })
