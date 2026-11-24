export const leaveStates = ['requested', 'granted', 'declined', 'withdrawn'] as const
export type LeaveState = (typeof leaveStates)[number]

const moves: Record<LeaveState, readonly LeaveState[]> = {
  requested: ['granted', 'declined', 'withdrawn'],
  granted: ['requested'],
  declined: ['requested'],
  withdrawn: ['requested'],
}

const managerMoves: readonly `${LeaveState}>${LeaveState}`[] = [
  'requested>granted',
  'requested>declined',
  'granted>requested',
]

export function canMove(from: LeaveState, to: LeaveState): boolean {
  return moves[from].includes(to)
}

export function needsManager(from: LeaveState, to: LeaveState): boolean {
  return managerMoves.includes(`${from}>${to}`)
}

export function isOpen(state: LeaveState): boolean {
  return state !== 'granted'
}

export const hasNext = (state: LeaveState) => leaveStates.some((to) => canMove(state, to))
