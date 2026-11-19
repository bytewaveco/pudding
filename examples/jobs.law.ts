import { domain, expect, law } from "pudding"
import { cancel, type JobState } from "./jobs.ts"

law("retrying cancellation has no further effect", domain<JobState>(), state => {
  expect(cancel(cancel(state))).toEqual(cancel(state))
})

law("cancellation preserves finished jobs and cancels all others", domain<JobState>(), state => {
  expect(cancel(state)).toEqual(state === "finished" ? "finished" : "cancelled")
})
