export type Light = "red" | "amber" | "green"

export function next(light: Light): Light {
  return light === "red" ? "green" : light === "green" ? "amber" : "red"
}
