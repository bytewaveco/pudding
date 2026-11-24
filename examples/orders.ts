export const statuses = ['draft', 'placed', 'shipped', 'cancelled'] as const
export type Status = (typeof statuses)[number]

export interface Order {
  status: Status
  paid: boolean
}

const next: Record<Status, readonly Status[]> = {
  draft: ['placed', 'cancelled'],
  placed: ['shipped', 'cancelled'],
  shipped: [],
  cancelled: [],
}

export function canMove(from: Status, to: Status): boolean {
  return next[from].includes(to)
}

export const isTerminal = (status: Status) => !statuses.some((to) => canMove(status, to))

export function ship(order: Order): Order {
  if (order.status !== 'placed' || !order.paid) throw new Error('this order cannot ship')
  return { ...order, status: 'shipped' }
}

export function label({ status, paid }: Order): string {
  return `${status}/${paid ? 'paid' : 'unpaid'}`
}
