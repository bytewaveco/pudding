// Render a report as text for the terminal or for GitHub Actions.

import { displayPath, type Finding, type LawReport, type Report, type Status } from "./runner.ts"

export type Reporter = "default" | "verbose" | "json" | "github"

const MARK: Record<Status, string> = { proved: "✓", checked: "~", sampled: "~", failed: "✗", skipped: "↓", todo: "□" }
const COLOR: Record<Status, number> = { proved: 32, checked: 33, sampled: 33, failed: 31, skipped: 2, todo: 2 }
const LABEL: Record<Status, string> = {
  proved: "proved", checked: "checked only", sampled: "sampled only", failed: "failed", skipped: "skipped", todo: "todo",
}
const ORDER: Status[] = ["proved", "checked", "sampled", "failed", "skipped", "todo"]

export function format(report: Report, options: { cwd: string; color: boolean; reporter: Reporter }): string {
  if (options.reporter === "json") return JSON.stringify(report, null, 2) + "\n"
  const paint = (code: number, text: string) => (options.color ? `\x1b[${code}m${text}\x1b[0m` : text)
  const dim = (text: string) => paint(2, text)
  const path = (file: string) => displayPath(options.cwd, file)
  const verbose = options.reporter === "verbose"
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
    lines.push(`   ${paint(COLOR[entry.status], MARK[entry.status])} ${entry.status === "skipped" || entry.status === "todo" ? dim(entry.name) : entry.name}${suffix}`)
    entry.findings.forEach(finding)
    for (const note of entry.notes) lines.push(dim(`      note: ${note}`))
  }

  const files = [...new Set(report.laws.map(entry => entry.file))]
  for (const file of files) {
    const laws = report.laws.filter(entry => entry.file === file)
    const failed = laws.some(entry => entry.status === "failed")
    const ran = laws.filter(entry => entry.status !== "skipped" && entry.status !== "todo")
    const quiet = (entry: LawReport) => !verbose && (entry.status === "skipped" || entry.status === "todo" || (entry.status === "proved" && !entry.notes.length))
    const mark = failed ? paint(31, "✗") : ran.length ? paint(32, "✓") : dim("↓")
    lines.push(` ${mark} ${path(file)} ${dim(`(${laws.length} ${laws.length === 1 ? "law" : "laws"})`)}`)
    for (const entry of laws) if (!quiet(entry)) law(entry)
  }
  if (files.length) lines.push("")
  for (const error of report.errors) lines.push(` ${paint(31, "error")} ${error}`)
  for (const warning of report.warnings) lines.push(` ${paint(33, "warning")} ${warning}`)
  if (report.errors.length || report.warnings.length) lines.push("")

  const counts = ORDER.filter(status => report.counts[status]).map(status => paint(COLOR[status], `${report.counts[status]} ${LABEL[status]}`))
  const version = /version ([\d.]+[^\s,]*)/.exec(report.lean)?.[1] ?? "unknown"
  lines.push(`  Laws    ${counts.join(dim(", ")) || "none"}`)
  lines.push(`  Proofs  ${report.obligations} ${report.obligations === 1 ? "theorem" : "theorems"}${report.cachedObligations ? ` (${report.cachedObligations} cached)` : ""}, ${report.cases.toLocaleString("en-US")} finite ${report.cases === 1 ? "case" : "cases"}, Lean ${version}`)
  lines.push(`  Time    ${report.durationMs} ms${report.replayed ? dim("  (nothing changed; result reused)") : ""}`)

  if (options.reporter === "github") {
    // Workflow commands turn into annotations on the lines concerned.
    const escape = (text: string) => text.replace(/%/g, "%25").replace(/\r/g, "%0D").replace(/\n/g, "%0A")
    const property = (text: string) => escape(text).replace(/:/g, "%3A").replace(/,/g, "%2C")
    for (const entry of report.laws) {
      for (const f of entry.findings) {
        const inputs = f.inputs && Object.keys(f.inputs).length ? ` with ${Object.entries(f.inputs).map(([name, value]) => `${name} = ${value}`).join(", ")}` : ""
        lines.push(`::error file=${property(path(f.file))},line=${f.line},col=${f.column},title=${property(entry.name)}::${escape(f.message + inputs)}`)
      }
    }
    for (const error of report.errors) lines.push(`::error::${escape(error)}`)
  }
  return lines.join("\n") + "\n"
}
