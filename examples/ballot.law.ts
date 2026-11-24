import { describe, domain, expect, law } from '@bytewaveco/pudding'

import { carries, count, type Ballot } from './ballot.ts'

describe('counting ballots', () => {
  law('every share is counted exactly once', domain<[Ballot, Ballot, Ballot]>(), ([a, b, c]) => {
    const counts = count([a, b, c])
    expect(counts.for + counts.against + counts.abstain).toEqual(a.shares + b.shares + c.shares)
  })

  law('the order of the ballots does not matter', domain<[Ballot, Ballot]>(), ([a, b]) => {
    expect(count([a, b])).toEqual(count([b, a]))
  })

  law(
    'an abstention never changes the outcome',
    domain<[Ballot, Ballot, bigint]>(),
    ([a, b, shares]) => {
      expect(carries([a, b, { choice: 'abstain', shares }])).toEqual(carries([a, b]))
    },
  )
})
