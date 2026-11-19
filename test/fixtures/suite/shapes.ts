export type Shape =
  | { kind: "square"; side: bigint }
  | { kind: "rect"; width: bigint; height: bigint }

export function area(shape: Shape): bigint {
  switch (shape.kind) {
    case "square":
      return shape.side * shape.side
    case "rect":
      return shape.width * shape.height
    default:
      throw new Error("unknown shape")
  }
}

export function scale(shape: Shape, factor: bigint): Shape {
  return shape.kind === "square"
    ? { kind: "square", side: shape.side * factor }
    : { ...shape, width: shape.width * factor, height: shape.height * factor }
}
