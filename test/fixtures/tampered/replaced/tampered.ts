class Fake<K, V> extends Map<K, V> { override get(key: K): V | undefined { return undefined } }
Map = Fake as MapConstructor
export function lookup(key: string): number | undefined { return new Map([["a", 1]]).get(key) }
