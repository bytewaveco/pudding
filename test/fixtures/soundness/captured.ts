// Three more ways a value read while the module loads can differ from the
// table's initial contents, although the table is back to them afterwards.
import { set } from "./setup.ts"

const viaAlias = { enabled: false }
const alias = viaAlias ?? {}
const aliasOn = alias.enabled = true
export const readViaAlias = viaAlias.enabled
const aliasOff = alias.enabled = false

const viaMethod = { active: false, configure: function (value: boolean) { this.active = value } }
const methodOn = viaMethod.configure(true)
export const readViaMethod = viaMethod.active
const methodOff = viaMethod.configure(false)

const viaHelper = { active: false } as const
const helperOn = set(viaHelper, true)
export const readViaHelper = viaHelper.active
const helperOff = set(viaHelper, false)

export const unused = [aliasOn, aliasOff, methodOn, methodOff, helperOn, helperOff]
