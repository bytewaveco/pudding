import { domain, expect, law } from "@bytewaveco/pudding"

// A proof script is text handed to Lean. These laws check that it can only
// ever be a proof of its own theorem.

law("a true law with an honest script", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: "intro h; simp_all; exact Int.mul_pos h.1 h.2" })

law("a true law with a script over several lines", domain<bigint>(), x => {
  expect(x + 0n).toEqual(x)
}, { proof: `intros
simp` })

law("a true law with comments, nested block comments, strings and primed names", domain<[bigint, bigint]>(), ([a, b]) => {
  if (a > 0n && b > 0n) expect(a * b > 0n).toBe(true)
}, { proof: `-- prove positivity (harmless comment with ) and --
/- nested /- block comment with ) and "unclosed -/ still comment -/
intro h'
have _ : "string with ) and -- and /-" = "string with ) and -- and /-" := rfl
have _ : ')' = ')' := rfl
simp_all
exact Int.mul_pos h'.1 h'.2 -- trailing comment` })

// The script proves its own law, then goes on to redefine what == means.
law("REJECTED: a script that carries on past its proof", domain<bigint>(), x => {
  if (x > 0n) expect(x + x > x).toBe(true)
}, { proof: `intro h; simp_all; omega
macro_rules | \`($a == $b) => \`(true)` })

// If the redefinition above took effect, this false law would be proved.
law("FALSE: a law after the tampering script", domain<bigint>(), x => {
  expect(x).toEqual(x + 1n)
})

law("REJECTED: a script that closes its own parentheses", domain<bigint>(), x => {
  expect(x).toEqual(x + 1n)
}, { proof: `sorry)
def helper : Nat := 0
example : True := by (trivial` })

law("REJECTED: a script that hides a parenthesis in a comment", domain<bigint>(), x => {
  expect(x).toEqual(x + 1n)
}, { proof: `-- (
sorry)
example : True := by (trivial -- )` })

law("REJECTED: an unfinished script", domain<bigint>(), x => {
  expect(x).toEqual(x + 1n)
}, { proof: "sorry" })
