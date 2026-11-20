;(Object.prototype as any).__defineGetter__("extra", () => 7n)
export function extra(box: { a: bigint }): bigint | undefined { return (box as { a: bigint; extra?: bigint }).extra }
