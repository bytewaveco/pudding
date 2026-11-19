// `read` runs while the module loads, before `flag` is initialized: importing this file throws.
export const ready = read()
const flag = true
function read() { return flag }
