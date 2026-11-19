export type Face = 1 | 2 | 3 | 4 | 5 | 6

/** The face on the opposite side of a die. */
export function opposite(face: Face): number {
  return 7 - face
}

export function isEven(face: Face): boolean {
  return face % 2 === 0
}
