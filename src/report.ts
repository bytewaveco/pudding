// Render a report as text for the terminal.

import { displayPath, type Finding, type LawReport, type Report, type Status } from "./runner.ts"

const MARK: Record<Status, string> = { proved: "✓", checked: "~", sampled: "~", failed: "✗" }
const COLOR: Record<Status, number> = { proved: 32, checked: 33, sampled: 33, failed: 31 }

export function format(report: Report, options: { cwd: string; color: boolean; verbose: boolean }): string {
  const paint = (code: number, text: string) => (options.color ? `\x1b[${code}m${text}\x1b[0m` : text)
  const dim = (text: string) => paint(2, text)
  const path = (file: string) => displayPath(options.cwd, file)
  const lines: string[] = []

  const finding = (f: Finding) => {
    lines.push(`      ${paint(31, f.message)}`)
    lines.push(dim(`      ${path(f.file)}:${f.line}:${f.column}${f.text ? `  ${f.text}` : ""}`))
    if (f.inputs && Object.keys(f.inputs).length) {
      lines.push(`      with ${Object.entries(f.inputs).map(([name, value]) => `${name} = ${value}`).join(", ")}`)
    }
    if (f.detail) for (const line of f.detail.split("\n")) lines.push(dim(`      ${line}`))
  }
  const law = (entry: LawReport) => {
    const suffix = entry.status === "checked" ? dim("  executed for every input, not proved")
      : entry.status === "sampled" ? dim("  executed on sampled inputs, not proved") : ""
    lines.push(`   ${paint(COLOR[entry.status], MARK[entry.status])} ${entry.name}${suffix}`)
    entry.findings.forEach(finding)
    for (const note of entry.notes) lines.push(dim(`      note: ${note}`))
  }

  const files = [...new Set(report.laws.map(entry => entry.file))]
  for (const file of files) {
    const laws = report.laws.filter(entry => entry.file === file)
    const failed = laws.some(entry => entry.status === "failed")
    const quiet = !options.verbose && laws.every(entry => entry.status === "proved" && !entry.notes.length)
    lines.push(` ${paint(failed ? 31 : 32, failed ? "✗" : "✓")} ${path(file)} ${dim(`(${laws.length} ${laws.length === 1 ? "law" : "laws"})`)}`)
    if (!quiet) laws.forEach(law)
  }
  if (files.length) lines.push("")
  for (const error of report.errors) lines.push(` ${paint(31, "error")} ${error}`)
  if (report.errors.length) lines.push("")

  const counts = (["proved", "checked", "sampled", "failed"] as const).filter(status => report.counts[status])
    .map(status => paint(COLOR[status], `${report.counts[status]} ${status === "checked" || status === "sampled" ? `${status} only` : status}`))
  const version = /version ([\d.]+\S*)/.exec(report.lean)?.[1]?.replace(/,$/, "") ?? "unknown"
  lines.push(`  Laws    ${counts.join(dim(", ")) || "none"}`)
  lines.push(`  Proofs  ${report.obligations} theorems${report.cachedObligations ? ` (${report.cachedObligations} cached)` : ""}, ${report.cases.toLocaleString("en-US")} finite cases, Lean ${version}`)
  lines.push(`  Time    ${report.durationMs} ms${report.replayed ? dim("  (nothing changed; result reused)") : ""}`)
  return lines.join("\n") + "\n"
}
