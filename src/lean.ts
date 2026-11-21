// Print obligations as Lean theorems and run Lean over them.

import { execFile } from "node:child_process"
import { createHash, randomUUID } from "node:crypto"
import { existsSync, mkdirSync, readFileSync, renameSync, rmSync, statSync, writeFileSync } from "node:fs"
import { mkdtemp, rm, writeFile } from "node:fs/promises"
import { availableParallelism, tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { setTimeout as sleep } from "node:timers/promises"
import { threadId } from "node:worker_threads"
import { cacheDirectory } from "./install.ts"
import * as ir from "./ir.ts"
import type { Binder, Expr, Scalar } from "./ir.ts"

/**
 * Minimal modules for finite laws checked purely by kernel reduction (`decide +kernel`),
 * without loading `Init.Grind` or `Init.Omega`.
 */
export const KERNEL_IMPORTS = [
  "Init.Core", "Init.Data.List.Basic", "Init.Data.String.Basic", "Init.Data.Int.DivMod", "Init.Data.Int.OfNat",
]

/**
 * The modules the generated theorems need. Importing only these starts Lean
 * several times faster than `import Init`, and they are what a trimmed Lean
 * runtime ships.
 */
export const FAST_IMPORTS = [
  "Init.Core", "Init.Omega", "Init.Grind", "Init.Data.List.Basic", "Init.Data.String.Basic", "Init.Data.Int.DivMod", "Init.Data.Int.OfNat",
]

/**
 * A slightly larger set for a second attempt. Measured against the whole of
 * `Init` on thousands of generated theorems, the fallback tactic proves
 * exactly as much under these imports.
 */
export const FALLBACK_IMPORTS = [...FAST_IMPORTS, "Init.Data.String.Lemmas.Basic", "Init.Data.String.Length"]

const header = (imports: readonly string[]) => ["prelude", ...imports.map(name => `import ${name}`)].join("\n")
export const KERNEL_HEADER = header(KERNEL_IMPORTS)
export const FAST_HEADER = header(FAST_IMPORTS)
export const FALLBACK_HEADER = header(FALLBACK_IMPORTS)
/** The whole core library, for proofs an author wrote. A trimmed runtime does not have it. */
export const FULL_HEADER = "import Init"

/** Pure kernel-reducible UTF-16 string definitions (no `grind`, `omega`, or `String.Lemmas`). */
const KERNEL_STRING_DEFS = `
def _p_utf16Units : List Char → Nat
  | [] => 0
  | c :: cs => (if c.val.toNat < 0x10000 then 1 else 2) + _p_utf16Units cs

noncomputable def _p_strLen (s : String) : Int := (_p_utf16Units s.toList : Int)

def _p_isPrefixOf : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && _p_isPrefixOf xs ys

noncomputable def _p_startsWith (s pre : String) : Bool := _p_isPrefixOf pre.toList s.toList
noncomputable def _p_endsWith (s suf : String) : Bool := _p_isPrefixOf suf.toList.reverse s.toList.reverse

def _p_containsList : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | pat@(_ :: _), c :: cs => _p_isPrefixOf pat (c :: cs) || _p_containsList pat cs

noncomputable def _p_includes (s sub : String) : Bool := _p_containsList sub.toList s.toList`.trim()

/**
 * Exact UTF-16 string helpers and `@[grind]` lemmas, emitted only when a
 * theorem uses symbolic string length or affix operations. Uses only modules
 * already shipped in `FALLBACK_IMPORTS` (no new runtime `.olean` packages).
 */
const STRING_PRELUDE = `${KERNEL_STRING_DEFS}

theorem _p_utf16Units_append (a b : List Char) : _p_utf16Units (a ++ b) = _p_utf16Units a + _p_utf16Units b := by
  induction a with
  | nil => simp [_p_utf16Units]
  | cons c cs ih => simp [_p_utf16Units, ih, Nat.add_assoc]

@[grind =, simp] theorem _p_strLen_append (a b : String) : _p_strLen (a ++ b) = _p_strLen a + _p_strLen b := by
  simp [_p_strLen, String.toList_append, _p_utf16Units_append]

theorem _p_strLen_nonneg (s : String) : 0 ≤ _p_strLen s := Int.natCast_nonneg _
grind_pattern _p_strLen_nonneg => _p_strLen s

theorem _p_utf16Units_eq_zero (cs : List Char) : _p_utf16Units cs = 0 ↔ cs = [] := by
  cases cs with
  | nil => simp [_p_utf16Units]
  | cons c cs =>
    constructor
    · intro h; unfold _p_utf16Units at h; split at h <;> omega
    · intro h; cases h

theorem _p_strLen_zero_iff (s : String) : _p_strLen s = 0 ↔ s = "" := by
  unfold _p_strLen
  constructor
  · intro h
    have h0 : _p_utf16Units s.toList = 0 := by omega
    have hl : s.toList = [] := (_p_utf16Units_eq_zero _).mp h0
    exact String.toList_inj.mp (by simpa using hl)
  · intro h; subst h; decide +kernel
grind_pattern _p_strLen_zero_iff => _p_strLen s

theorem _p_isPrefixOf_append (a b : List Char) : _p_isPrefixOf a (a ++ b) = true := by
  induction a with
  | nil => rfl
  | cons c cs ih => simp [_p_isPrefixOf, ih]

@[grind =, simp] theorem _p_startsWith_append (a b : String) : _p_startsWith (a ++ b) a = true := by
  simp [_p_startsWith, String.toList_append, _p_isPrefixOf_append]

@[grind =, simp] theorem _p_startsWith_self (a : String) : _p_startsWith a a = true := by
  have := _p_startsWith_append a ""; simpa using this

@[grind =, simp] theorem _p_startsWith_empty (a : String) : _p_startsWith a "" = true := by
  simp [_p_startsWith, _p_isPrefixOf]

@[grind =, simp] theorem _p_endsWith_append (a b : String) : _p_endsWith (a ++ b) b = true := by
  simp [_p_endsWith, String.toList_append, List.reverse_append, _p_isPrefixOf_append]

@[grind =, simp] theorem _p_endsWith_self (a : String) : _p_endsWith a a = true := by
  have := _p_endsWith_append "" a; simpa using this

@[grind =, simp] theorem _p_endsWith_empty (a : String) : _p_endsWith a "" = true := by
  simp [_p_endsWith, _p_isPrefixOf]

theorem _p_containsList_of_prefix (p s : List Char) : _p_isPrefixOf p s = true → _p_containsList p s = true := by
  cases p with
  | nil => intro _; cases s <;> rfl
  | cons x xs =>
    cases s with
    | nil => intro h; cases h
    | cons y ys => intro h; simp [_p_containsList, h]

theorem _p_containsList_append_left (p a b : List Char) : _p_containsList p b = true → _p_containsList p (a ++ b) = true := by
  induction a with
  | nil => intro h; exact h
  | cons c cs ih =>
    cases p with
    | nil => intro _; cases cs <;> rfl
    | cons x xs => intro h; simp only [_p_containsList, Bool.or_eq_true, List.cons_append]; right; exact ih h

@[grind =, simp] theorem _p_includes_self (a : String) : _p_includes a a = true :=
  _p_containsList_of_prefix _ _ (by simpa [_p_startsWith] using _p_startsWith_self a)

@[grind =, simp] theorem _p_includes_empty (a : String) : _p_includes a "" = true := by
  unfold _p_includes; cases a.toList <;> rfl

@[grind =, simp] theorem _p_includes_append_left (a b : String) : _p_includes (a ++ b) a = true :=
  _p_containsList_of_prefix _ _ (by simpa [_p_startsWith] using _p_startsWith_append a b)

@[grind =, simp] theorem _p_includes_append_right (a b : String) : _p_includes (a ++ b) b = true := by
  unfold _p_includes; rw [String.toList_append]
  exact _p_containsList_append_left _ _ _ (by simpa [_p_includes] using _p_includes_self b)

theorem _p_includes_of_startsWith (s p : String) : _p_startsWith s p = true → _p_includes s p = true :=
  _p_containsList_of_prefix _ _
grind_pattern _p_includes_of_startsWith => _p_startsWith s p

theorem _p_isPrefixOf_len (a b : List Char) : _p_isPrefixOf a b = true → _p_utf16Units a ≤ _p_utf16Units b := by
  induction a generalizing b with
  | nil => intro _; simp [_p_utf16Units]
  | cons x xs ih =>
    cases b with
    | nil => intro h; cases h
    | cons y ys =>
      simp only [_p_isPrefixOf, Bool.and_eq_true, beq_iff_eq]
      rintro ⟨rfl, h⟩; have := ih ys h; simp only [_p_utf16Units]; omega

theorem _p_startsWith_len (s pre : String) : _p_startsWith s pre = true → _p_strLen pre ≤ _p_strLen s := by
  intro h; have := _p_isPrefixOf_len pre.toList s.toList h; unfold _p_strLen; omega
grind_pattern _p_startsWith_len => _p_startsWith s pre

theorem _p_utf16Units_reverse (a : List Char) : _p_utf16Units a.reverse = _p_utf16Units a := by
  induction a with
  | nil => rfl
  | cons c cs ih => simp [_p_utf16Units, _p_utf16Units_append, ih, Nat.add_comm]

theorem _p_endsWith_len (s suf : String) : _p_endsWith s suf = true → _p_strLen suf ≤ _p_strLen s := by
  intro h
  have := _p_isPrefixOf_len suf.toList.reverse s.toList.reverse h
  rw [_p_utf16Units_reverse, _p_utf16Units_reverse] at this
  unfold _p_strLen; omega
grind_pattern _p_endsWith_len => _p_endsWith s suf

theorem _p_startsWith_concat (s t pre : String) : _p_startsWith s pre = true → _p_startsWith (s ++ t) pre = true := by
  unfold _p_startsWith; rw [String.toList_append]
  generalize pre.toList = p; generalize s.toList = a; generalize t.toList = b
  induction p generalizing a with
  | nil => intro _; rfl
  | cons x xs ih =>
    cases a with
    | nil => intro h; cases h
    | cons y ys =>
      simp only [_p_isPrefixOf, Bool.and_eq_true, beq_iff_eq, List.cons_append]
      rintro ⟨rfl, h⟩; exact ⟨rfl, ih ys h⟩
grind_pattern _p_startsWith_concat => _p_startsWith (s ++ t) pre

theorem _p_endsWith_concat (s t suf : String) : _p_endsWith t suf = true → _p_endsWith (s ++ t) suf = true := by
  unfold _p_endsWith; rw [String.toList_append, List.reverse_append]
  generalize suf.toList.reverse = p; generalize t.toList.reverse = a; generalize s.toList.reverse = b
  induction p generalizing a with
  | nil => intro _; rfl
  | cons x xs ih =>
    cases a with
    | nil => intro h; cases h
    | cons y ys =>
      simp only [_p_isPrefixOf, Bool.and_eq_true, beq_iff_eq, List.cons_append]
      rintro ⟨rfl, h⟩; exact ⟨rfl, ih ys h⟩
grind_pattern _p_endsWith_concat => _p_endsWith (s ++ t) suf`.trim()

const usesStringPrelude = (statement: string) => /_p_(?:strLen|startsWith|endsWith|includes)\b/.test(statement)

/** Pure kernel-reducible list length definition (no `grind` or `omega`). */
const KERNEL_LIST_DEFS = `def _p_listLen {α : Type} (xs : List α) : Int := (xs.length : Int)`

/**
 * List length helpers and `@[grind]` lemmas, emitted only when a theorem uses
 * arbitrary-length `List` operations or recursive `def`s. Uses only `FAST_IMPORTS`.
 */
const LIST_PRELUDE = `${KERNEL_LIST_DEFS}

theorem _p_listLen_nonneg {α : Type} (xs : List α) : 0 ≤ _p_listLen xs := Int.natCast_nonneg _
grind_pattern _p_listLen_nonneg => _p_listLen xs

@[grind =, simp] theorem _p_listLen_nil {α : Type} : _p_listLen ([] : List α) = 0 := rfl
@[grind =, simp] theorem _p_listLen_cons {α : Type} (x : α) (xs : List α) : _p_listLen (x :: xs) = 1 + _p_listLen xs := by
  simp [_p_listLen]; omega
@[grind =, simp] theorem _p_listLen_append {α : Type} (xs ys : List α) : _p_listLen (xs ++ ys) = _p_listLen xs + _p_listLen ys := by
  simp [_p_listLen]
@[grind =, simp] theorem _p_listLen_map {α β : Type} (f : α → β) (xs : List α) : _p_listLen (xs.map f) = _p_listLen xs := by
  simp [_p_listLen]
@[grind =, simp] theorem _p_listLen_reverse {α : Type} (xs : List α) : _p_listLen xs.reverse = _p_listLen xs := by
  simp [_p_listLen]

theorem _p_listLen_filter_le {α : Type} (p : α → Bool) (xs : List α) : _p_listLen (xs.filter p) ≤ _p_listLen xs := by
  unfold _p_listLen
  induction xs with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons]
    split <;> simp <;> omega
grind_pattern _p_listLen_filter_le => _p_listLen (xs.filter p)

theorem _p_listLen_zero_iff {α : Type} (xs : List α) : _p_listLen xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [_p_listLen]
  | cons h t => simp [_p_listLen]; omega
grind_pattern _p_listLen_zero_iff => _p_listLen xs

theorem _p_listLen_tail {α : Type} (xs : List α) : _p_listLen xs ≠ 0 → _p_listLen xs.tail = _p_listLen xs - 1 := by
  cases xs with
  | nil => intro h; exact absurd rfl h
  | cons h t => intro _; simp [_p_listLen]
grind_pattern _p_listLen_tail => _p_listLen xs.tail`.trim()

const usesListPrelude = (statement: string) => /\b_p_listLen\b/.test(statement)

export function printDef(def: ir.FnDef): string {
  const params = def.params.map(p => `(${p.name} : ${leanType(p.ty)})`).join(" ")
  const body = printExpr(def.body)
  const listParam = def.params.find(p => ir.isListTy(p.ty))
  const listStep = listParam ? ` | (cases ${listParam.name} <;> simp_all [_p_listLen] <;> omega)` : ""
  return `def ${def.name} ${params} : ${leanType(def.retTy)} :=\n  ${body}\ntermination_by ${def.measure}\ndecreasing_by\n  all_goals (first | (simp_all [_p_listLen]; omega)${listStep})`
}

export const DEFAULT_TACTIC = "grind"
const FINITE_TACTIC = "decide +kernel"
/** Tried, under the fallback imports, on statements the default tactic could not close. */
const FALLBACK_TACTIC = "first | grind | (intros; simp_all; done) | (intros; simp_all <;> omega)"
const MAX_TERM_SIZE = 200_000
/**
 * The most text one expression may come to. A value fed back into itself in a
 * loop multiplies in size with every round, and Lean's time grows with it:
 * about five seconds at this size, and minutes a few rounds later.
 */
const MAX_TERM_TEXT = 120_000
/**
 * The longest a string may become where a law is checked value by value. Lean's
 * kernel compares strings a character at a time and gives up on long ones,
 * somewhere past 800 characters, after working on them for many seconds.
 */
const MAX_STRING_LENGTH = 500
/** The most characters an integer comes to as text, where every input has a short list of values. */
const INTEGER_TEXT = 24
/** How long one Lean process may run: this much, plus a share for each theorem in its file. */
const FILE_TIMEOUT_MS = 30_000
const THEOREM_TIMEOUT_MS = 10_000
const MAX_SPECIALIZATIONS = 512

/** Top-level Lean declaration and command keywords that never belong inside a tactic proof block. */
const FORBIDDEN_SCRIPT_KEYWORDS = new Set([
  "axiom", "theorem", "lemma", "example", "def", "abbrev", "opaque", "constant",
  "inductive", "coinductive", "structure", "class", "instance",
  "import", "namespace", "section", "universe", "variable", "attribute",
  "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation",
  "infix", "infixl", "infixr", "prefix", "postfix", "declare_syntax_cat",
  "initialize", "builtin_initialize",
])

const OPEN_DELIMS: Record<string, string> = { "(": ")", "[": "]", "{": "}", "⟨": "⟩" }
const CLOSE_DELIMS: Record<string, string> = { ")": "(", "]": "[", "}": "{", "⟩": "⟨" }
const IDENT_START = /^[\p{L}_]$/u
const IDENT_CONT = /^[\p{L}\p{N}_'?!\u2070-\u209f]$/u

/**
 * Lex a Lean 4 proof script and verify it is a single, self-contained tactic
 * block. Comments (`--`, nested `/- ... -/`), string literals, character
 * literals and `«quoted names»` are tokenized according to Lean's grammar so
 * harmless uses are accepted while delimiter escapes, unterminated tokens,
 * interpolated strings and Lean commands/declarations are rejected.
 */
export function scriptProblem(script: string): string | undefined {
  const stack: string[] = []
  let tokens = 0
  let afterDot = false
  let i = 0
  const n = script.length

  while (i < n) {
    const ch = script[i]!
    // Whitespace
    if (ch === " " || ch === "\t" || ch === "\r" || ch === "\n") {
      afterDot = false
      i++
      continue
    }
    // Line comment: `--` to end of line
    if (ch === "-" && script[i + 1] === "-") {
      afterDot = false
      i += 2
      while (i < n && script[i] !== "\n") i++
      continue
    }
    // Nested block comment: `/- ... -/` (including doc comments `/--` and `/-!`)
    if (ch === "/" && script[i + 1] === "-") {
      afterDot = false
      let depth = 1
      i += 2
      while (i < n && depth > 0) {
        if (script[i] === "/" && script[i + 1] === "-") { depth++; i += 2 }
        else if (script[i] === "-" && script[i + 1] === "/") { depth--; i += 2 }
        else i++
      }
      if (depth > 0) return "unterminated block comment in the proof script"
      continue
    }
    // Raw string literal: `r"..."`, `r#"..."#`, etc.
    if (ch === "r") {
      let j = i + 1
      while (j < n && script[j] === "#") j++
      if (script[j] === '"') {
        const hashes = j - (i + 1)
        const close = '"' + "#".repeat(hashes)
        const end = script.indexOf(close, j + 1)
        if (end < 0) return "unterminated string literal in the proof script"
        i = end + close.length
        tokens++
        afterDot = false
        continue
      }
    }
    // String literal: `"..."` with Lean backslash escapes
    if (ch === '"') {
      i++
      let closed = false
      while (i < n) {
        const c = script[i]!
        if (c === "\\") {
          if (i + 1 >= n) return "unterminated string literal in the proof script"
          i += 2
          continue
        }
        if (c === '"') { closed = true; i++; break }
        i++
      }
      if (!closed) return "unterminated string literal in the proof script"
      tokens++
      afterDot = false
      continue
    }
    // Character literal: `'c'` or `'\...'` (only outside identifiers)
    if (ch === "'") {
      i++
      if (i >= n || script[i] === "\n" || script[i] === "'") return "unterminated character literal in the proof script"
      if (script[i] === "\\") {
        i++
        if (i >= n) return "unterminated character literal in the proof script"
        const esc = script[i]!
        if (esc === "x") {
          if (!/^[0-9a-fA-F]{2}'/.test(script.slice(i + 1, i + 4))) return "unterminated character literal in the proof script"
          i += 4
        } else if (esc === "u") {
          if (!/^[0-9a-fA-F]{4}'/.test(script.slice(i + 1, i + 6))) return "unterminated character literal in the proof script"
          i += 6
        } else {
          i++
          if (script[i] !== "'") return "unterminated character literal in the proof script"
          i++
        }
      } else {
        const cp = script.codePointAt(i)!
        i += cp > 0xffff ? 2 : 1
        if (script[i] !== "'") return "unterminated character literal in the proof script"
        i++
      }
      tokens++
      afterDot = false
      continue
    }
    // French-quoted identifier: `«...»`
    if (ch === "«") {
      const end = script.indexOf("»", i + 1)
      if (end < 0) return "unterminated «quoted name» in the proof script"
      i = end + 1
      tokens++
      afterDot = false
      continue
    }
    if (ch === "»") return "unexpected `»` in the proof script"
    // Lean `#command` (e.g. `#eval`, `#check`, `#print`, `#exit`)
    if (ch === "#" && i + 1 < n && IDENT_START.test(script[i + 1]!)) {
      return "a proof script may not contain Lean commands"
    }
    // Delimiters: `()`, `[]`, `{}`, `⟨⟩`
    if (ch in OPEN_DELIMS) {
      stack.push(ch)
      i++
      tokens++
      afterDot = false
      continue
    }
    if (ch in CLOSE_DELIMS) {
      const want = CLOSE_DELIMS[ch]!
      if (stack.length === 0 || stack[stack.length - 1] !== want) {
        return ch === ")" || stack[stack.length - 1] === "("
          ? "the parentheses in the proof script do not balance"
          : "the delimiters in the proof script do not balance"
      }
      stack.pop()
      i++
      tokens++
      afterDot = false
      continue
    }
    // Identifiers and keywords
    if (IDENT_START.test(ch)) {
      const start = i
      i++
      while (i < n && IDENT_CONT.test(script[i]!)) i++
      const word = script.slice(start, i)
      // Interpolated strings (`s!"..."`, `m!"..."`, etc.) embed arbitrary expressions inside quotes.
      if (word.endsWith("!") && script[i] === '"') {
        return "interpolated strings are not allowed in proof scripts"
      }
      if (!afterDot && FORBIDDEN_SCRIPT_KEYWORDS.has(word)) {
        return `a proof script may not contain \`${word}\``
      }
      tokens++
      afterDot = false
      continue
    }
    // Dot tracks qualified names (e.g. `Nat.def` or projection) vs standalone keywords
    afterDot = ch === "."
    i++
    tokens++
  }

  if (stack.length > 0) {
    return stack.includes("(")
      ? "the parentheses in the proof script do not balance"
      : "the delimiters in the proof script do not balance"
  }
  if (tokens === 0) return "the proof script is empty"
  return undefined
}

/** How a statement is proved: by evaluating every case, by the default automation, or by the author's script. */
export function proofKind(statement: string): "finite" | "automatic" | "authored" {
  if (statement.endsWith(` := by ${FINITE_TACTIC}`)) return "finite"
  return statement.endsWith(` := by ${DEFAULT_TACTIC}`) || statement.endsWith(` := by ${FALLBACK_TACTIC}`) ? "automatic" : "authored"
}

/** The same statement with the stronger, slower automation. Only meaningful for an automatic statement. */
export function withFallback(statement: string): string {
  return statement.slice(0, -DEFAULT_TACTIC.length) + FALLBACK_TACTIC
}

/** Collect nonlinear operations (products of two unknowns, divisions/remainders by an unknown) from an expression DAG. */
function collectNonLinear(root: Expr): { divs: [Expr, Expr][]; muls: [Expr, Expr][]; strs: Expr[] } {
  const visited = new Set<Expr>()
  const divs: [Expr, Expr][] = []
  const muls: [Expr, Expr][] = []
  const strs: Expr[] = []
  const stack: Expr[] = [root]
  while (stack.length) {
    const e = stack.pop()!
    if (e.t !== "op" || visited.has(e)) continue
    visited.add(e)
    const [a, b] = e.args as [Expr, Expr]
    if ((e.op === "div" || e.op === "mod" || e.op === "fdiv") && b.t !== "lit") divs.push([a, b])
    else if (e.op === "mul" && a.t !== "lit" && b.t !== "lit") muls.push([a, b])
    else if (e.op === "str" && a.t !== "lit") strs.push(a)
    for (const arg of e.args) stack.push(arg)
  }
  return { divs, muls, strs }
}

/** Format a small IR expression using the law's input names for diagnostics. */
function describeExpr(e: Expr, labels: ReadonlyMap<string, string>, depth = 0): string {
  if (e.t === "var") return labels.get(e.name) ?? e.name
  if (e.t === "lit") return typeof e.value === "bigint" ? `${e.value}n` : JSON.stringify(e.value)
  if (depth >= 2) return "…"
  const sub = (x: Expr) => describeExpr(x, labels, depth + 1)
  const [a, b] = e.args as [Expr, Expr]
  switch (e.op) {
    case "add": return `(${sub(a)} + ${sub(b)})`
    case "sub": return `(${sub(a)} - ${sub(b)})`
    case "mul": return `(${sub(a)} * ${sub(b)})`
    case "neg": return `(-${sub(a)})`
    case "div": case "fdiv": return `(${sub(a)} / ${sub(b)})`
    case "mod": return `(${sub(a)} % ${sub(b)})`
    default: return "…"
  }
}

/** Human-readable list of nonlinear operations in an obligation that likely stopped linear automation. */
export function describeNonLinearOps(guard: Expr, claim: Expr, binders: readonly Binder[]): string | undefined {
  const labels = new Map(binders.map(b => [b.name, b.label]))
  const { divs, muls, strs } = collectNonLinear(implication(guard, claim))
  const notes = new Set<string>()
  for (const [, d] of divs) notes.add(`division/remainder by unknown \`${describeExpr(d, labels)}\``)
  for (const [a, b] of muls) notes.add(`product of unknowns \`${describeExpr(a, labels)} * ${describeExpr(b, labels)}\``)
  for (const a of strs) notes.add(`converting unknown \`${describeExpr(a, labels)}\` to text`)
  if (!notes.size) return undefined
  return [...notes].slice(0, 3).join(", ")
}

/**
 * Third-attempt tactic for statements that contain nonlinear multiplication or
 * division/remainder by an unknown: tries algebraic div/mod identities,
 * sign-aware product lemmas (including square splits), monotonicity lemmas, and
 * automatic sign splitting on unknown divisors and dividends — all within the
 * existing bundled `FALLBACK_IMPORTS`.
 */
export function withNonLinear(statement: string, guard: Expr, claim: Expr): string | undefined {
  if (!statement.endsWith(` := by ${DEFAULT_TACTIC}`)) return undefined
  // Extract the theorem's bound Int variables from the parameter prefix so we never reference specialized-away vars.
  const params = /^(?: \([a-zA-Z_]\w* : (?:Bool|Int|String|List (?:Bool|Int|String))\))*/.exec(statement)?.[0] ?? ""
  const bound = new Set<string>()
  for (const match of params.matchAll(/\(([a-zA-Z_]\w*) : Int\)/g)) bound.add(match[1]!)
  if (!bound.size) return undefined

  const { divs, muls } = collectNonLinear(implication(guard, claim))
  const printable = (e: Expr): string | undefined => {
    for (const v of ir.freeVariables(e)) if (!bound.has(v)) return undefined
    try {
      const s = printExpr(e)
      return s.length <= 40 && !s.includes("let ") ? s : undefined
    } catch {
      return undefined
    }
  }

  const divPairs: [string, string][] = []
  const seenDiv = new Set<string>()
  for (const [a, d] of divs) {
    const sa = printable(a), sd = printable(d)
    if (!sa || !sd) continue
    const key = `${sa}\0${sd}`
    if (seenDiv.has(key)) continue
    seenDiv.add(key)
    divPairs.push([sa, sd])
    if (divPairs.length >= 2) break
  }

  const mulPairs: [string, string][] = []
  const seenMul = new Set<string>()
  for (const [a, b] of muls) {
    const sa = printable(a), sb = printable(b)
    if (!sa || !sb) continue
    const key = `${sa}\0${sb}`
    if (seenMul.has(key)) continue
    seenMul.add(key)
    mulPairs.push([sa, sb])
    if (mulPairs.length >= 3) break
  }

  if (!divPairs.length && !mulPairs.length) return undefined

  const branches: string[] = []
  // 1. Algebraic div/mod & ring identities.
  branches.push(`(intros; simp_all [Int.mul_tdiv_add_tmod, Int.mul_ediv_add_emod, Int.mul_fdiv_add_fmod, Int.mul_tdiv_cancel_left, Int.mul_comm]; (first | done | omega | grind))`)

  // 2. Sign-aware product bounds and monotonicity.
  if (mulPairs.length) {
    const steps: string[] = ["intros", "simp_all"]
    mulPairs.forEach(([a, b], idx) => {
      if (a === b) {
        steps.push(`(have _sq${idx} : (${a}) < 0 ∨ 0 ≤ (${a}) := by omega)`)
        steps.push(`rcases _sq${idx} with _ | _`)
        steps.push(`all_goals ((try have _mp${idx} := Int.mul_pos_of_neg_of_neg (a := ${a}) (b := ${a}) (by omega) (by omega)); (try have _mn${idx} := Int.mul_nonneg (a := ${a}) (b := ${a}) (by omega) (by omega)))`)
      } else {
        steps.push(`(try have _mp${idx} := Int.mul_pos (a := ${a}) (b := ${b}) (by omega) (by omega))`)
        steps.push(`(try have _mn${idx} := Int.mul_nonneg (a := ${a}) (b := ${b}) (by omega) (by omega))`)
        steps.push(`(try have _mnn${idx} := Int.mul_pos_of_neg_of_neg (a := ${a}) (b := ${b}) (by omega) (by omega))`)
        steps.push(`(try have _mpn${idx} := Int.mul_neg_of_pos_of_neg (a := ${a}) (b := ${b}) (by omega) (by omega))`)
        steps.push(`(try have _mnp${idx} := Int.mul_neg_of_neg_of_pos (a := ${a}) (b := ${b}) (by omega) (by omega))`)
      }
    })
    steps.push(`all_goals (first | assumption | omega | grind | (apply Int.mul_le_mul_of_nonneg_left <;> omega) | (apply Int.mul_le_mul_of_nonneg_right <;> omega) | (apply Int.mul_lt_mul_of_pos_left <;> omega) | (apply Int.mul_lt_mul_of_pos_right <;> omega))`)
    branches.push(`(${steps.join("; ")})`)
  }

  // 3. Automatic divisor and dividend sign splits for truncated & floored division/remainder.
  if (divPairs.length) {
    const [a, d] = divPairs[0]!
    const divTactic = [
      "intros",
      "simp_all",
      `(have _sd : (${d}) < 0 ∨ (${d}) = 0 ∨ 0 < (${d}) := by omega)`,
      "rcases _sd with _ | _ | _",
      `all_goals ((try omega); (try ((have _sa : (${a}) < 0 ∨ 0 ≤ (${a}) := by omega); rcases _sa with _ | _)))`,
      `all_goals ((try have _d0 := Int.tdiv_nonneg (a := ${a}) (b := ${d}) (by omega) (by omega)); (try have _d1 := Int.tdiv_nonneg (a := -(${a})) (b := ${d}) (by omega) (by omega)); (try have _d2 := Int.tdiv_nonneg (a := ${a}) (b := -(${d})) (by omega) (by omega)); (try have _d3 := Int.tdiv_nonneg (a := -(${a})) (b := -(${d})) (by omega) (by omega)); (try have _m0 := Int.tmod_nonneg (${d}) (a := ${a}) (by omega)); (try have _m1 := Int.tmod_nonneg (${d}) (a := -(${a})) (by omega)); (try have _m2 := Int.tmod_nonneg (-(${d})) (a := ${a}) (by omega)); (try have _m3 := Int.tmod_nonneg (-(${d})) (a := -(${a})) (by omega)); (try have _l0 := Int.tmod_lt_of_pos (${a}) (b := ${d}) (by omega)); (try have _l1 := Int.tmod_lt_of_pos (-(${a})) (b := ${d}) (by omega)); (try have _l2 := Int.tmod_lt_of_pos (${a}) (b := -(${d})) (by omega)); (try have _l3 := Int.tmod_lt_of_pos (-(${a})) (b := -(${d})) (by omega)); (try have _s0 := Int.tdiv_le_self (${d}) (a := ${a}) (by omega)); (try have _e0 := Int.ediv_nonneg (a := ${a}) (b := ${d}) (by omega) (by omega)); (try have _e1 := Int.emod_nonneg (${a}) (b := ${d}) (by omega)); (try have _e2 := Int.emod_lt_of_pos (${a}) (b := ${d}) (by omega)); simp_all [Int.neg_tdiv, Int.tdiv_neg, Int.neg_tmod, Int.tmod_neg, Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg, Int.fdiv_eq_ediv_of_nonneg, Int.mul_tdiv_add_tmod, Int.mul_ediv_add_emod, Int.mul_fdiv_add_fmod, Int.mul_comm]; (first | done | assumption | omega | grind))`,
    ].join("; ")
    branches.push(`(${divTactic})`)
  }

  return statement.slice(0, -DEFAULT_TACTIC.length) + `(first | ${branches.join(" | ")})`
}

export class TooLarge extends Error {}

function leanString(text: string): string {
  let out = '"'
  for (const char of text) {
    const code = char.codePointAt(0)!
    if (char === '"' || char === "\\") out += "\\" + char
    else if (code >= 0x20 && code < 0x7f) out += char
    else if (code < 0x10000) out += "\\u" + code.toString(16).padStart(4, "0")
    else out += char
  }
  return out + '"'
}

function leanScalar(value: Scalar): string {
  if (Array.isArray(value)) return `[${value.map(leanScalar).join(", ")}]`
  if (typeof value === "boolean") return String(value)
  if (typeof value === "bigint") return `(${value} : Int)`
  return leanString(value as string)
}

/** Minimum printed length before a shared subexpression is bound with `let`. */
const CSE_MIN_LENGTH = 24
/** Finite-only theorems above this many cases quantify consecutive linear integer ranges with `grind`. */
const FINITE_QUANTIFY_THRESHOLD = 256
/** Max concurrent Lean chunks where `--incr-load` improves wall time without memory contention. */
const SNAPSHOT_MAX_CHUNKS = 8

function printOp(e: Extract<Expr, { t: "op" }>, args: string[]): string {
  const [a = "", b = "", c = ""] = args
  switch (e.op) {
    case "not": return `(!${a})`
    case "and": return `(${a} && ${b})`
    case "or": return `(${a} || ${b})`
    case "eq": return `(${a} == ${b})`
    case "lt": return `(decide (${a} < ${b}))`
    case "le": return `(decide (${a} ≤ ${b}))`
    case "add": return `(${a} + ${b})`
    case "sub": return `(${a} - ${b})`
    case "mul": return `(${a} * ${b})`
    case "neg": return `(-${a})`
    case "concat": return `(${a} ++ ${b})`
    case "str": return `(toString ${a})`
    case "strlen": return `(_p_strLen ${a})`
    case "startsWith": return `(_p_startsWith ${a} ${b})`
    case "endsWith": return `(_p_endsWith ${a} ${b})`
    case "includes": return `(_p_includes ${a} ${b})`
    case "ite": return `(if ${a} then ${b} else ${c})`
    case "listLit": return args.length === 0 ? `([] : ${leanType(e.ty)})` : `[${args.join(", ")}]`
    case "listLen": return `(_p_listLen ${a})`
    case "listConcat": return `(${a} ++ ${b})`
    case "listReverse": return `(${a}.reverse)`
    case "listElem": return `(${a}.contains ${b})`
    case "listHead": return `(${a}.headD ${e.ty === "bool" ? "false" : e.ty === "int" ? "(0 : Int)" : '""'})`
    case "listTail": return `(${a}.tail)`
    case "listMap": return `(${a}.map fun ${e.param} => ${b})`
    case "listFilter": return `(${a}.filter fun ${e.param} => ${b})`
    case "listAny": return `(${a}.any fun ${e.param} => ${b})`
    case "listAll": return `(${a}.all fun ${e.param} => ${b})`
    case "listFold": return `(${a}.foldl (fun ${e.acc} ${e.param} => ${c}) ${b})`
    case "call": return args.length ? `(${e.fn} ${args.join(" ")})` : `(${e.fn})`
    case "fdiv": {
      // Lean's `/` on integers rounds toward minus infinity when the divisor
      // is positive, so a literal divisor needs no case split.
      const divisor = e.args[1]!
      if (divisor.t === "lit" && (divisor.value as bigint) > 0n) return `(${a} / ${divisor.value})`
      if (divisor.t === "lit" && (divisor.value as bigint) < 0n) return `((-${a}) / ${-(divisor.value as bigint)})`
      return `(Int.fdiv ${a} ${b})`
    }
    case "div":
    case "mod": {
      // BigInt division truncates toward zero and the remainder takes the sign
      // of the dividend. With a literal divisor both are written with Lean's
      // `/` and `%` on non-negative operands, which the arithmetic tactics
      // understand. A zero divisor is excluded by a separate obligation.
      const divisor = e.args[1]!
      const symbol = e.op === "div" ? "/" : "%"
      if (divisor.t === "lit" && divisor.value !== 0n) {
        const magnitude = (divisor.value as bigint) < 0n ? -(divisor.value as bigint) : (divisor.value as bigint)
        const flip = e.op === "div" && (divisor.value as bigint) < 0n
        const body = `(if (0 : Int) ≤ ${a} then ${a} ${symbol} ${magnitude} else -((-${a}) ${symbol} ${magnitude}))`
        return flip ? `(-${body})` : body
      }
      return `(Int.${e.op === "div" ? "tdiv" : "tmod"} ${a} ${b})`
    }
  }
}

/**
 * Print an expression DAG with value-based CSE (`let _vN := ...`) so loops,
 * duplicate subtrees from separate branches, and literal `div`/`mod` (which
 * mentions its dividend three times) do not expand exponentially.
 */
function printExpr(root: Expr): string {
  const visited = new Set<Expr>()
  const postorder: Expr[] = []
  const stack: [Expr, boolean][] = [[root, false]]
  const bodyIdxOf = (e: Extract<Expr, { t: "op" }>) => (e.param !== undefined ? (e.op === "listFold" ? 2 : 1) : -1)
  while (stack.length) {
    const [e, expanded] = stack.pop()!
    if (expanded) {
      postorder.push(e)
      continue
    }
    if (visited.has(e)) continue
    visited.add(e)
    if (visited.size > MAX_TERM_SIZE) throw new TooLarge("the translated expression is too large to check")
    stack.push([e, true])
    if (e.t === "op") {
      const skip = bodyIdxOf(e)
      for (let i = e.args.length - 1; i >= 0; i--) if (i !== skip) stack.push([e.args[i]!, false])
    }
  }
  const intern = new Map<string, number>()
  const idOf = new Map<Expr, number>()
  const nodeOf: Expr[] = []
  const lambdaPrinted = new Map<Expr, string>()
  for (const e of postorder) {
    let key: string
    if (e.t === "var") key = `v:${e.ty}:${e.name}`
    else if (e.t === "lit") key = `l:${e.ty}:${typeof e.value === "string" ? JSON.stringify(e.value) : String(e.value)}`
    else {
      const skip = bodyIdxOf(e)
      if (skip >= 0) {
        const bodyStr = printExpr(e.args[skip]!)
        lambdaPrinted.set(e, bodyStr)
        const argIds = e.args.map((a, idx) => (idx === skip ? `B:${bodyStr}` : String(idOf.get(a)!))).join(",")
        key = `o:${e.op}:${e.param ?? ""}:${e.acc ?? ""}:${argIds}`
      } else {
        key = `o:${e.op}:${e.fn ?? ""}:${e.ty}:${e.args.map(a => idOf.get(a)!).join(",")}`
      }
    }
    let id = intern.get(key)
    if (id === undefined) {
      id = nodeOf.length
      intern.set(key, id)
      nodeOf.push(e)
    }
    idOf.set(e, id)
  }
  const rootId = idOf.get(root)!
  const refs = new Int32Array(nodeOf.length)
  for (const e of nodeOf) {
    if (e.t !== "op") continue
    const skip = bodyIdxOf(e)
    e.args.forEach((arg, idx) => { if (idx !== skip) refs[idOf.get(arg)!]!++ })
    if ((e.op === "div" || e.op === "mod") && e.args[1]!.t === "lit" && e.args[1]!.value !== 0n && e.args[0]!.t === "op") {
      refs[idOf.get(e.args[0]!)!]! += 2
    }
  }
  const lets: string[] = []
  const printed = new Array<string>(nodeOf.length)
  let totalChars = 0
  for (let id = 0; id < nodeOf.length; id++) {
    const e = nodeOf[id]!
    if (e.t === "var") { printed[id] = e.name; continue }
    if (e.t === "lit") { printed[id] = leanScalar(e.value); continue }
    const skip = bodyIdxOf(e)
    const args = e.args.map((arg, idx) => (idx === skip ? lambdaPrinted.get(e)! : printed[idOf.get(arg)!]!))
    const text = printOp(e, args)
    if (refs[id]! >= 2 && text.length >= CSE_MIN_LENGTH && id !== rootId) {
      const name = `_v${lets.length}`
      const binding = `let ${name} := ${text}`
      totalChars += binding.length + 2
      if (totalChars > MAX_TERM_TEXT) throw new TooLarge("the translated expression is too large to check")
      lets.push(binding)
      printed[id] = name
    } else {
      if (text.length > MAX_TERM_TEXT) throw new TooLarge("the translated expression is too large to check")
      printed[id] = text
    }
  }
  const body = printed[rootId]!
  const full = lets.length ? `(${lets.join("; ")}; ${body})` : body
  if (full.length > MAX_TERM_TEXT) throw new TooLarge("the translated expression is too large to check")
  return full
}

/** An upper bound on the length of any string the expression builds, given inputs with listed values. */
function longestString(body: Expr, inputs: readonly Binder[]): number {
  const given = new Map(inputs.map(input => [input.name, Math.max(0, ...(input.domain ?? []).map(value => typeof value === "string" ? value.length : 0))]))
  const memo = new Map<Expr, number>()
  const postorder: Expr[] = []
  const visited = new Set<Expr>()
  const stack: [Expr, boolean][] = [[body, false]]
  while (stack.length) {
    const [e, expanded] = stack.pop()!
    if (e.t !== "op") continue
    if (expanded) {
      postorder.push(e)
      continue
    }
    if (visited.has(e)) continue
    visited.add(e)
    stack.push([e, true])
    for (let i = e.args.length - 1; i >= 0; i--) stack.push([e.args[i]!, false])
  }
  let longest = 0
  const lengthOf = (e: Expr): number => {
    if (e.t === "var") return given.get(e.name) ?? 0
    if (e.t === "lit") {
      const own = typeof e.value === "string" ? e.value.length : 0
      if (own > longest) longest = own
      return own
    }
    return memo.get(e) ?? 0
  }
  for (const e of postorder) {
    if (e.t !== "op") continue
    const parts = e.args.map(lengthOf)
    const own = e.ty !== "str" ? 0
      : e.op === "concat" ? parts[0]! + parts[1]!
      : e.op === "ite" ? Math.max(parts[1]!, parts[2]!)
      : INTEGER_TEXT
    memo.set(e, own)
    if (own > longest) longest = own
  }
  lengthOf(body)
  return longest
}

function leanType(ty: ir.Ty): string {
  return { bool: "Bool", int: "Int", str: "String", list_bool: "List Bool", list_int: "List Int", list_str: "List String" }[ty]
}

/** The proposition `guard → claim` as a single boolean. */
function implication(guard: Expr, claim: Expr): Expr {
  return ir.or(ir.not(guard), claim)
}

export interface Check {
  /** Everything after the theorem name. Also the cache key, together with the Lean version. */
  statement: string
  /** Number of concrete cases the theorem covers when it is decided by evaluation. */
  cases: number
  /** Printed recursive `def` declarations required by this theorem, if any. */
  defs?: string
}

/**
 * Theorems that together state `∀ binders, guard → claim`.
 *
 * When every input is finite there is one theorem, decided by evaluating all
 * cases in Lean's kernel. Otherwise the finite inputs are specialized away and
 * each remaining theorem quantifies over the unbounded ones.
 */
/** The bounds of a finite integer input whose values are consecutive, when it has more than a couple. */
function consecutive(binder: Binder): [bigint, bigint] | undefined {
  const values = binder.domain
  if (binder.ty !== "int" || !values || values.length < 3) return undefined
  const sorted = (values as bigint[]).toSorted((a, b) => (a < b ? -1 : a > b ? 1 : 0))
  return sorted.every((value, i) => i === 0 || value === sorted[i - 1]! + 1n) ? [sorted[0]!, sorted.at(-1)!] : undefined
}

/** Variables divided by, multiplied nonlinearly, or formatted as text (which tactics cannot decide), in O(|DAG|) time and memory. */
function nonLinearVars(root: Expr): Set<string> {
  const visited = new Set<Expr>()
  const roots: Expr[] = []
  const stack: Expr[] = [root]
  while (stack.length) {
    const e = stack.pop()!
    if (e.t !== "op" || visited.has(e)) continue
    visited.add(e)
    const [a, b] = e.args as [Expr, Expr]
    if (e.op === "str") roots.push(a)
    else if (e.op === "div" || e.op === "mod" || e.op === "fdiv") roots.push(b)
    else if (e.op === "mul" && a.t !== "lit" && b.t !== "lit") roots.push(a, b)
    for (const arg of e.args) stack.push(arg)
  }
  const bad = new Set<string>()
  const marked = new Set<Expr>()
  while (roots.length) {
    const e = roots.pop()!
    if (e.t === "var") { bad.add(e.name); continue }
    if (e.t !== "op" || marked.has(e)) continue
    marked.add(e)
    for (const arg of e.args) roots.push(arg)
  }
  return bad
}

function usedDefs(root: Expr, defs: readonly ir.FnDef[] | undefined): string | undefined {
  if (!defs?.length) return undefined
  const directCalls = (e: Expr): Set<string> => {
    const names = new Set<string>()
    const seen = new Set<Expr>()
    const stack: Expr[] = [e]
    while (stack.length) {
      const cur = stack.pop()!
      if (cur.t !== "op" || seen.has(cur)) continue
      seen.add(cur)
      if (cur.op === "call" && cur.fn) names.add(cur.fn)
      for (const arg of cur.args) stack.push(arg)
    }
    return names
  }
  const rootCalls = directCalls(root)
  if (!rootCalls.size) return undefined
  const byName = new Map(defs.map(d => [d.name, d]))
  const ordered: ir.FnDef[] = []
  const visiting = new Set<string>()
  const emitted = new Set<string>()
  const emit = (name: string) => {
    if (emitted.has(name) || visiting.has(name)) return
    const def = byName.get(name)
    if (!def) return
    visiting.add(name)
    for (const dep of directCalls(def.body)) emit(dep)
    visiting.delete(name)
    emitted.add(name)
    ordered.push(def)
  }
  for (const name of rootCalls) emit(name)
  return ordered.length ? ordered.map(printDef).join("\n\n") : undefined
}

export function checksFor(binders: readonly Binder[], guard: Expr, claim: Expr, tactic: string | undefined, defs?: readonly ir.FnDef[]): Check[] {
  const body = implication(guard, claim)
  const defsText = usedDefs(body, defs)
  const free = ir.freeVariables(body)
  const used = binders.filter(b => free.has(b.name))
  const allFinite = used.every(b => b.domain)
  const finiteCases = allFinite ? used.reduce((n, b) => n * b.domain!.length, 1) : 0
  // An integer input over a run of consecutive values does not have to be
  // split into cases: its bounds can be stated instead, which the arithmetic
  // tactics use directly. For large finite-only spaces (e.g. [1..200]^2),
  // quantifying consecutive linear integer ranges is an order of magnitude
  // faster than `decide +kernel`.
  const bounded = new Map<string, [bigint, bigint]>()
  if (!allFinite || (tactic === undefined && finiteCases > FINITE_QUANTIFY_THRESHOLD)) {
    const nonLinear = nonLinearVars(body)
    for (const binder of used) {
      const range = consecutive(binder)
      if (range && !nonLinear.has(binder.name)) bounded.set(binder.name, range)
    }
  }
  const finiteCheck = (): Check[] => {
    if (longestString(body, used) > MAX_STRING_LENGTH) {
      throw new TooLarge(`a string here can grow past ${MAX_STRING_LENGTH} characters, which is too large to check`)
    }
    let text = printExpr(body)
    for (const binder of [...used].reverse()) {
      text = `([${binder.domain!.map(leanScalar).join(", ")}].all fun ${binder.name} => ${text})`
    }
    return [{ statement: ` : ${text} = true := by ${FINITE_TACTIC}`, cases: finiteCases, ...(defsText ? { defs: defsText } : {}) }]
  }
  if (allFinite && bounded.size === 0) return finiteCheck()
  const finite = used.filter(b => b.domain && !bounded.has(b.name))
  const symbolic = used.filter(b => !b.domain || bounded.has(b.name))
  for (const [name, [low, high]] of bounded) {
    const input = ir.variable(name, "int")
    guard = ir.and(ir.and(ir.le(ir.lit(low), input), ir.le(input, ir.lit(high))), guard)
  }
  const combinations = finite.reduce((n, b) => n * b.domain!.length, 1)
  if (combinations > MAX_SPECIALIZATIONS) {
    // When all inputs are actually finite, fall back to direct enumeration if specialization would overflow.
    if (allFinite) return finiteCheck()
    throw new TooLarge(`the finite inputs have ${combinations} combinations alongside unbounded ones; the limit is ${MAX_SPECIALIZATIONS}`)
  }
  // An author's script goes inside parentheses, so that it has to be a complete
  // tactic sequence and nothing after it can be read as part of it. Common
  // leading indentation is stripped so multiline template literals align cleanly.
  const dedent = (text: string): string => {
    const raw = text.replace(/^\r?\n/, "").replace(/\r?\n\s*$/, "").split(/\r?\n/)
    const indents = raw.filter(l => l.trim().length > 0).map(l => /^ */.exec(l)![0].length)
    const min = indents.length ? Math.min(...indents) : 0
    return raw.map(l => l.slice(min)).join("\n")
  }
  const script = tactic === undefined ? DEFAULT_TACTIC : `(\n  ${dedent(tactic).split("\n").join("\n  ")}\n)`
  const checks: Check[] = []
  const visit = (index: number, values: Map<string, Expr>) => {
    if (index < finite.length) {
      for (const value of finite[index]!.domain!) visit(index + 1, new Map(values).set(finite[index]!.name, ir.lit(value)))
      return
    }
    const g = ir.substitute(guard, values)
    const c = ir.substitute(claim, values)
    if (implication(g, c) === ir.TRUE) return
    const remaining = ir.freeVariables(implication(g, c))
    const parameters = symbolic.filter(b => remaining.has(b.name)).map(b => ` (${b.name} : ${leanType(b.ty)})`).join("")
    const proposition = g === ir.TRUE ? `${printExpr(c)} = true` : `${printExpr(g)} = true → ${printExpr(c)} = true`
    // Attribute the full covered finite domain once on the first emitted check so skipped trivial specializations stay counted.
    checks.push({
      statement: `${parameters} : ${proposition} := by ${script}`,
      cases: allFinite && checks.length === 0 ? finiteCases : 0,
      ...(defsText ? { defs: defsText } : {}),
    })
  }
  visit(0, new Map())
  return checks
}

export interface LeanOutcome {
  ok: boolean
  /** Lean's message when the theorem was rejected. */
  message: string
}

interface LeanMessage {
  severity: string
  pos?: { line: number }
  data: string
}

/** Lean was stopped because it ran past its time limit. */
class LeanTimeout extends Error {}

/**
 * How many Lean processes may run at once on this machine, counting every
 * Pudding run. Vitest proves each law file in a worker of its own, and
 * without a shared limit each of them would start a Lean per core.
 */
const SLOTS = availableParallelism()
const slotDirectory = join(tmpdir(), `pudding-slots-${process.getuid?.() ?? "user"}`)
/** Waiting this long for a slot means the slots are stuck, not busy, and Lean then runs unpaced. */
const SLOT_WAIT_MS = 120_000
/** The slots this thread holds, given back if it exits while Lean runs. */
const held = new Map<string, string>()
process.on("exit", () => {
  for (const [file, token] of held) release(file, token)
})

/**
 * Wait for one of the machine's Lean slots, and return what gives it back. A
 * slot is a file created exclusively, holding its owner's process id and the
 * time by which its Lean will have been stopped, counted from when the slot
 * was taken. A slot whose owner has exited or is past that time is taken
 * over. Slots only pace the work: where they cannot be used, Lean runs unpaced.
 */
async function slot(timeout: number): Promise<() => void> {
  if (!slotsUsable()) return () => {}
  const started = Date.now()
  for (let wait = 5; Date.now() - started < SLOT_WAIT_MS; wait = Math.min(wait * 2, 50)) {
    for (let n = 0; n < SLOTS; n++) {
      const file = join(slotDirectory, String(n))
      const token = `${process.pid} ${Date.now() + timeout} ${randomUUID()}`
      try {
        writeFileSync(file, token, { flag: "wx" })
        held.set(file, token)
        return () => {
          held.delete(file)
          release(file, token)
        }
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== "EEXIST") return () => {}
        // Only the claim judged abandoned is removed, never one made since.
        const claim = abandoned(file)
        if (claim !== undefined) release(file, claim)
      }
    }
    await sleep(wait)
  }
  return () => {}
}

function slotsUsable(): boolean {
  try {
    mkdirSync(slotDirectory, { recursive: true, mode: 0o700 })
    // A directory another user made first would let them hold every slot.
    return process.getuid === undefined || statSync(slotDirectory).uid === process.getuid()
  } catch {
    return false
  }
}

/** Give a slot back only while it is still this run's: one taken over belongs to another run now. */
function release(file: string, token: string): void {
  try {
    if (readFileSync(file, "utf8") === token) rmSync(file, { force: true })
  } catch {
    // Already gone.
  }
}

/** The claim in a slot, when its owner has exited or overrun its deadline. */
function abandoned(file: string): string | undefined {
  let claim: string
  try {
    claim = readFileSync(file, "utf8")
  } catch {
    return undefined
  }
  const [pid, deadline] = claim.split(" ").map(Number)
  try {
    // An empty slot is being written, or its owner stopped before writing it.
    if (!pid || !deadline) return Date.now() - statSync(file).mtimeMs > 1_000 ? claim : undefined
    if (Date.now() > deadline) return claim
    process.kill(pid, 0)
    return undefined
  } catch (error) {
    return (error as NodeJS.ErrnoException).code === "ESRCH" ? claim : undefined
  }
}

/** Cached Lean header snapshots per `(lean binary, stdlib, header)`, published atomically as a directory holding both `.snap` and `.snap.deps`. */
const snapshotPromises = new Map<string, Promise<string | undefined>>()
const failedSnapshots = new Set<string>()

function headerSnapshotDir(lean: string, header: string): string | undefined {
  if (header === FULL_HEADER) return undefined
  try {
    const stat = statSync(lean)
    const coreOlean = join(dirname(dirname(lean)), "lib", "lean", "Init", "Core.olean")
    const libSig = existsSync(coreOlean) ? (() => { const s = statSync(coreOlean); return `${s.mtimeMs}:${s.size}` })() : ""
    const id = createHash("sha256").update(`${lean}:${stat.mtimeMs}:${stat.size}\0${libSig}\0${header}`).digest("hex").slice(0, 24)
    return join(cacheDirectory(), "snapshots", id)
  } catch {
    return undefined
  }
}

async function ensureHeaderSnapshot(lean: string, header: string, directory: string): Promise<string | undefined> {
  const targetDir = headerSnapshotDir(lean, header)
  if (!targetDir || failedSnapshots.has(targetDir)) return undefined
  const targetSnap = join(targetDir, "header.snap")
  if (existsSync(targetSnap) && existsSync(`${targetSnap}.deps`)) return targetSnap
  const pending = snapshotPromises.get(targetDir)
  if (pending) return pending
  const created = (async () => {
    const stagingDir = `${targetDir}.tmp.${process.pid}.${threadId}.${randomUUID().slice(0, 8)}`
    try {
      mkdirSync(stagingDir, { recursive: true })
      const probe = join(directory, `.snap-${process.pid}-${threadId}.lean`)
      const stagedSnap = join(stagingDir, "header.snap")
      await writeFile(probe, `${header}\n#check Nat\n`)
      const release = await slot(30_000)
      try {
        await new Promise<void>((resolve, reject) => {
          execFile(lean, [`--incr-header-save=${stagedSnap}`, "-DmaxErrors=0", "--json", probe], { maxBuffer: 1 << 26, timeout: 20_000, killSignal: "SIGKILL" }, error => {
            if (error) reject(error)
            else resolve()
          })
        })
      } finally {
        release()
      }
      if (existsSync(stagedSnap) && existsSync(`${stagedSnap}.deps`)) {
        try {
          renameSync(stagingDir, targetDir)
        } catch {
          // Another process published the same snapshot directory concurrently.
          rmSync(stagingDir, { recursive: true, force: true })
        }
        if (existsSync(targetSnap) && existsSync(`${targetSnap}.deps`)) return targetSnap
      }
      failedSnapshots.add(targetDir)
    } catch {
      // Snapshots are purely an optimization; remember failure in-process and fall back to loading imports normally.
      failedSnapshots.add(targetDir)
    } finally {
      rmSync(stagingDir, { recursive: true, force: true })
      snapshotPromises.delete(targetDir)
    }
    return undefined
  })()
  snapshotPromises.set(targetDir, created)
  return created
}

function runFile(lean: string, source: string, directory: string, name: string, timeout: number, snapshot?: string): Promise<LeanMessage[]> {
  return new Promise((resolve, reject) => {
    const file = join(directory, name)
    writeFile(file, source).then(() => {
      const invoke = (snap: string | undefined) => {
        const args = [...(snap ? [`--incr-load=${snap}`] : []), "-DmaxErrors=0", "--json", file]
        // Lean stops reporting after 100 errors unless told otherwise, and a theorem it never reported on must not pass for proved.
        execFile(lean, args, { maxBuffer: 1 << 28, timeout, killSignal: "SIGKILL" }, (error, stdout, stderr) => {
          if (error?.killed) return reject(new LeanTimeout())
          if (error && typeof (error as NodeJS.ErrnoException).code === "string") {
            return reject(new Error(`could not run Lean at ${lean}: ${error.message}`))
          }
          const messages: LeanMessage[] = []
          for (const line of stdout.split("\n")) {
            if (!line.startsWith("{")) continue
            try {
              messages.push(JSON.parse(line) as LeanMessage)
            } catch {
              // Not a diagnostic line.
            }
          }
          if (error && !messages.some(m => m.severity === "error")) {
            // If a cached header snapshot is corrupt or incompatible, discard its directory and retry normally once.
            if (snap) {
              try { rmSync(dirname(snap), { recursive: true, force: true }) } catch { /* ignore */ }
              return invoke(undefined)
            }
            return reject(new Error(`Lean exited abnormally: ${(stderr || stdout).trim().slice(0, 2000)}`))
          }
          resolve(messages)
        })
      }
      invoke(snapshot)
    }, reject)
  })
}

/** The axioms of Lean's own logic. A proof that rests on anything else, `sorry` above all, is not a proof. */
const ACCEPTED_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"])

async function runChunk(lean: string, header: string, statements: string[], directory: string, name: string, strict: boolean, timeout: number, snapshot?: string, defs?: string): Promise<LeanOutcome[]> {
  // Each theorem is followed by a question about it: which axioms does it
  // rest on? A theorem counts as proved only when Lean reports no error for
  // it *and* answers that question acceptably. Silence is never taken for
  // success, and neither is an unfinished proof, which Lean only warns about.
  const kernelOnly = header === KERNEL_HEADER
  const lines = header.split("\n")
  if (statements.some(usesStringPrelude) || (defs && usesStringPrelude(defs))) {
    lines.push("", ...(kernelOnly ? KERNEL_STRING_DEFS : STRING_PRELUDE).split("\n"))
  }
  if (defs || statements.some(usesListPrelude)) {
    lines.push("", ...(kernelOnly ? KERNEL_LIST_DEFS : LIST_PRELUDE).split("\n"))
  }
  const defsStart = defs ? lines.length + 1 : 0
  if (defs) lines.push("", ...defs.split("\n"))
  const firstLine: number[] = []
  const askedAt: number[] = []
  for (const [i, statement] of statements.entries()) {
    firstLine.push(lines.length + 1)
    lines.push(...`theorem c${i}${statement}`.split("\n"))
    askedAt.push(lines.length + 1)
    lines.push(`#print axioms c${i}`)
  }
  // The file ends with a command that always answers, to show that Lean reached the end.
  const sentinel = lines.length + 1
  lines.push("#check Nat")
  const messages = await runFile(lean, lines.join("\n") + "\n", directory, name, timeout, snapshot)
  if (!messages.some(message => message.severity === "information" && message.pos?.line === sentinel)) {
    throw new Error("Lean stopped before it had checked every theorem, so no result can be trusted")
  }
  const outcomes: LeanOutcome[] = statements.map(() => ({ ok: false, message: "" }))
  const failed = new Set<number>()
  const reject = (index: number, text: string) => {
    const outcome = outcomes[index]!
    outcome.message = outcome.message ? outcome.message + "\n" + text : text
    failed.add(index)
  }
  for (const message of messages) {
    const line = message.pos?.line ?? 0
    let lo = 0, hi = firstLine.length - 1, index = -1
    while (lo <= hi) {
      const mid = (lo + hi) >>> 1
      if (firstLine[mid]! <= line) { index = mid; lo = mid + 1 } else hi = mid - 1
    }
    if (message.severity === "error") {
      // An error after the last theorem means something in the file disturbed what follows it. Trust none of it.
      if (line >= sentinel) return statements.map(() => ({ ok: false, message: `Lean reported an error after the theorems: ${message.data}` }))
      if (index < 0) {
        if (defs && line >= defsStart) {
          return statements.map(() => ({ ok: false, message: `termination: ${message.data}` }))
        }
        throw new Error(`Lean rejected the generated preamble: ${message.data}`)
      }
      // An error on the question itself only repeats that the theorem above it failed.
      if (line !== askedAt[index] || !failed.has(index)) reject(index, message.data)
    } else if (index >= 0 && line === askedAt[index] && message.severity === "information") {
      const listed = /depends on axioms: \[([^\]]*)\]/.exec(message.data)
      const foreign = listed ? listed[1]!.split(",").map(axiom => axiom.trim()).filter(axiom => axiom && !ACCEPTED_AXIOMS.has(axiom)) : []
      if (foreign.includes("sorryAx")) {
        if (!failed.has(index)) reject(index, "the proof is unfinished: it uses `sorry`")
      } else if (foreign.length) reject(index, `the proof rests on ${foreign.map(axiom => `\`${axiom}\``).join(", ")}, which Pudding does not accept`)
      else if (listed || /does not depend on any axioms/.test(message.data)) outcomes[index]!.ok = true
    }
  }
  for (const index of failed) outcomes[index]!.ok = false
  // A file holding an author's script must be clean throughout: an error anywhere means Lean read something as more than a proof.
  if (strict && messages.some(message => message.severity === "error")) for (const outcome of outcomes) outcome.ok = false
  for (const outcome of outcomes) if (!outcome.ok && !outcome.message) outcome.message = "Lean did not confirm this theorem"
  return outcomes
}

export async function prove(lean: string, header: string, statements: string[], processes = availableParallelism(), alone = false, defs?: string): Promise<LeanOutcome[]> {
  if (!statements.length) return []
  const allFinite = !defs && statements.every(s => proofKind(s) === "finite")
  const effectiveHeader = header === FAST_HEADER
    ? (allFinite ? KERNEL_HEADER : (statements.some(usesStringPrelude) || (defs && usesStringPrelude(defs))) ? FALLBACK_HEADER : header)
    : header
  const directory = await mkdtemp(join(tmpdir(), "pudding-"))
  try {
    const chunks: string[][] = []
    if (alone) for (const statement of statements) chunks.push([statement])
    else {
      // Starting Lean costs little next to proving, so spread the work widely.
      const workers = Math.max(1, Math.min(processes, Math.ceil(statements.length / 8)))
      const size = Math.ceil(statements.length / workers)
      for (let i = 0; i < statements.length; i += size) chunks.push(statements.slice(i, i + size))
    }
    // Reuse a cached header snapshot when running a modest number of chunks
    // (avoids memory contention on wide fan-out while cutting startup in half).
    const snapshot = chunks.length <= SNAPSHOT_MAX_CHUNKS ? await ensureHeaderSnapshot(lean, effectiveHeader, directory) : undefined
    // Lean bounds its tactics by work done, not by the clock, and reading a
    // huge theorem is not bounded at all. A file that runs past its time is
    // tried again one theorem at a time, so that only the slow one goes unproved.
    const attempt = async (chunk: string[], file: string): Promise<LeanOutcome[]> => {
      const timeout = FILE_TIMEOUT_MS + THEOREM_TIMEOUT_MS * chunk.length
      try {
        // The slot is held while Lean runs, never while waiting for another.
        const release = await slot(timeout + 10_000)
        try {
          return await runChunk(lean, effectiveHeader, chunk, directory, file, alone, timeout, snapshot, defs)
        } finally {
          release()
        }
      } catch (error) {
        if (!(error instanceof LeanTimeout)) throw error
        if (chunk.length === 1) return [{ ok: false, message: `Lean did not finish within ${timeout / 1000} seconds` }]
        const outcomes: LeanOutcome[] = []
        for (const [n, statement] of chunk.entries()) outcomes.push(...await attempt([statement], `${file.replace(/\.lean$/, "")}_${n}.lean`))
        return outcomes
      }
    }
    // At most `processes` files at a time from this run, each starting as soon
    // as one before it finishes, and all within the machine's Lean slots.
    const results: LeanOutcome[][] = []
    let next = 0
    let stopped = false
    const worker = async () => {
      while (!stopped && next < chunks.length) {
        const i = next++
        try {
          results[i] = await attempt(chunks[i]!, `Proof${i}.lean`)
        } catch (error) {
          stopped = true
          throw error
        }
      }
    }
    await Promise.all(Array.from({ length: Math.min(Math.max(1, processes), chunks.length) }, worker))
    return results.flat()
  } finally {
    await rm(directory, { recursive: true, force: true })
  }
}

/** The Lean source for a set of statements, for inspection. */
export function render(header: string, statements: string[], comments?: ReadonlyMap<string, string>, defs?: readonly (string | undefined)[]): string {
  const allDefsText = defs ? defs.filter((d): d is string => Boolean(d)).join("\n\n") : ""
  const allFinite = !allDefsText && statements.length > 0 && statements.every(s => proofKind(s) === "finite")
  const needsStrings = statements.some(usesStringPrelude) || usesStringPrelude(allDefsText)
  const needsLists = Boolean(allDefsText) || statements.some(usesListPrelude)
  const effectiveHeader = header === FAST_HEADER
    ? (allFinite ? KERNEL_HEADER : needsStrings ? FALLBACK_HEADER : header)
    : header
  const kernelOnly = effectiveHeader === KERNEL_HEADER
  const prelude = [
    needsStrings ? (kernelOnly ? KERNEL_STRING_DEFS : STRING_PRELUDE) : "",
    needsLists ? (kernelOnly ? KERNEL_LIST_DEFS : LIST_PRELUDE) : "",
  ].filter(Boolean).join("\n\n")
  const groups = new Map<string, number[]>()
  for (let i = 0; i < statements.length; i++) {
    const key = defs?.[i] ?? ""
    let list = groups.get(key)
    if (!list) groups.set(key, list = [])
    list.push(i)
  }
  let groupId = 0
  const sections: string[] = []
  for (const [defBlock, indices] of groups) {
    const theorems = indices.map(i => {
      const statement = statements[i]!
      const note = comments?.get(defBlock ? `${defBlock}\0${statement}` : statement) ?? comments?.get(statement)
      const comment = note ? note.split(/\r?\n/).map(line => `-- ${line}`).join("\n") + "\n" : ""
      return `${comment}theorem c${i}${statement}`
    }).join("\n\n")
    if (!defBlock) sections.push(theorems)
    else {
      const ns = `_g${groupId++}`
      sections.push(`namespace ${ns}\n\n${defBlock}\n\n${theorems}\n\nend ${ns}`)
    }
  }
  return effectiveHeader + (prelude ? `\n\n${prelude}` : "") + "\n\n" + sections.join("\n\n") + "\n"
}
