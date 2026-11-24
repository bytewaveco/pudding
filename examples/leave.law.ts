import { domain, expect, law } from '@bytewaveco/pudding'

import { canMove, hasNext, isOpen, needsManager, type LeaveState } from './leave.ts'

law('granted leave is the only state that is not open', domain<LeaveState>(), (state) => {
  expect(isOpen(state)).toEqual(state !== 'granted')
})

law(
  'granting leave, or taking it back, takes a manager',
  domain<[LeaveState, LeaveState]>(),
  ([from, to]) => {
    if (canMove(from, to) && (from === 'granted' || to === 'granted')) {
      expect(needsManager(from, to)).toEqual(true)
    }
  },
)

law("a manager's moves are moves that exist", domain<[LeaveState, LeaveState]>(), ([from, to]) => {
  if (needsManager(from, to)) expect(canMove(from, to)).toEqual(true)
})

law('no request is ever stuck', domain<LeaveState>(), (state) => {
  expect(hasNext(state)).toEqual(true)
})

law('an employee can always withdraw a fresh request, and start over afterwards', () => {
  expect(canMove('requested', 'withdrawn') && !needsManager('requested', 'withdrawn')).toEqual(true)
  expect(canMove('withdrawn', 'requested') && !needsManager('withdrawn', 'requested')).toEqual(true)
})
