export type JobState = "queued" | "running" | "cancelled" | "finished"

export function cancel(state: JobState): JobState {
  return state === "finished" ? state : "cancelled"
}
