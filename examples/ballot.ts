export type Choice = "for" | "against" | "abstain"

export interface Ballot {
  choice: Choice
  shares: bigint
}

/** Adds each ballot's shares to the count of its choice. */
export function count(ballots: readonly Ballot[]) {
  const counts = { for: 0n, against: 0n, abstain: 0n }
  for (const ballot of ballots) counts[ballot.choice] += ballot.shares
  return counts
}

/** Whether the motion carries: more shares for it than against it, abstentions aside. */
export function carries(ballots: readonly Ballot[]): boolean {
  const counts = count(ballots)
  return counts.for > counts.against
}
