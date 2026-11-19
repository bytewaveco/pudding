function rule(): string {
  let text = "=-"
  for (let round = 0; round < 8; round++) text = text + text
  return text
}

/** Two long rules with a marker between them, the marker chosen last. */
export function banner(wide: boolean): string {
  return rule() + (wide ? "<" : ">") + rule()
}

/** The same text, with the whole of it chosen at once. */
export function framed(wide: boolean): string {
  return wide ? rule() + "<" + rule() : rule() + ">" + rule()
}

export function short(wide: boolean): string {
  return "=-" + (wide ? "<" : ">") + "=-"
}
