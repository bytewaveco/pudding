import { domain, expect, law } from "@bytewaveco/pudding"
import { area, scale, type Shape } from "./shapes.ts"

law("scaling by one changes nothing", domain<Shape>(), shape => {
  expect(scale(shape, 1n)).toEqual(shape)
})

law("scaling multiplies the area by the square of the factor", domain<[Shape, bigint]>(), ([shape, factor]) => {
  expect(area(scale(shape, factor))).toEqual(area(shape) * factor * factor)
})

law("FALSE: scaling doubles the area", domain<Shape>(), shape => {
  expect(area(scale(shape, 2n))).toEqual(area(shape) * 2n)
})
