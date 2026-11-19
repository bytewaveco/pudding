export type Flags = Record<string, boolean>
export const tag = Symbol("tag")
export type Tagged<T> = { [tag]: T }
