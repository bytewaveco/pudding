const { prototype: every } = Object
;(every as { extra?: bigint }).extra = 7n
export function extra(box: { a: bigint }): bigint | undefined { return (box as { a: bigint; extra?: bigint }).extra }
