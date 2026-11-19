/** Where a request for time off stands. */
export const leaveStates = ["requested", "granted", "declined", "withdrawn"] as const
export type LeaveState = (typeof leaveStates)[number]

const moves: Record<LeaveState, readonly LeaveState[]> = {
  requested: ["granted", "declined", "withdrawn"],
  granted: ["requested"],
  declined: ["requested"],
  withdrawn: ["requested"],
}

/** Moves only a manager may make. Everything else is the employee's own. */
const managerMoves: readonly `${LeaveState}>${LeaveState}`[] = ["requested>granted", "requested>declined", "granted>requested"]

export function canMove(from: LeaveState, to: LeaveState): boolean {
  return moves[from].includes(to)
}

export function needsManager(from: LeaveState, to: LeaveState): boolean {
  return managerMoves.includes(`${from}>${to}`)
}

/** Granted leave is fixed until a manager reopens it. */
export function isOpen(state: LeaveState): boolean {
  return state !== "granted"
}

/** Whether anything can still happen to a request in this state. */
export const hasNext = (state: LeaveState) => leaveStates.some(to => canMove(state, to))
