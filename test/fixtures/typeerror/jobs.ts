export type JobState = "queued" | "finished"
export const cancel = (state: JobState): JobState => (state === "finished" ? state : "queued")
