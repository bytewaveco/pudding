import { describe, domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { countPositive, doubleAll, nonTerminating, positives, sumList, sumRec, sumToRec } from "./lists.ts"

describe("arbitrary-length arrays and folds", () => {
  law("map, filter, reverse, concat and spread preserve length and structure for any array", domain<[bigint[], bigint[]]>(), ([xs, ys]) => {
    expect(doubleAll(xs).length).toEqual(xs.length)
    expect(positives(xs).length <= xs.length).toBe(true)
    expect(xs.toReversed().toReversed()).toEqual(xs)
    expect(xs.toReversed().length).toEqual(xs.length)
    expect(xs.concat([])).toEqual(xs)
    expect([...xs].length).toEqual(xs.length)
    if (xs.length <= 1000000 && ys.length <= 1000000) expect(xs.concat(ys).length).toEqual(xs.length + ys.length)
    expect(Array.isArray(xs)).toBe(true)
  })

  law("for...of fold agrees with reduce on arbitrary-length arrays", domain<bigint[]>(), xs => {
    expect(sumList(xs)).toEqual(xs.reduce((acc, x) => acc + x, 0n))
  })

  law("for...of fold distributes over concat with an induction script", domain<[bigint[], bigint[]]>(), ([xs, ys]) => {
    expect(sumList(xs.concat(ys))).toEqual(sumList(xs) + sumList(ys))
  }, {
    proof: `
      simp only [beq_iff_eq]
      have aux : ∀ (a b : List Int) (init : Int),
        (a ++ b).foldl (fun acc x => acc + x) init = b.foldl (fun acc x => acc + x) (a.foldl (fun acc x => acc + x) init) := by
        intro a; induction a with
        | nil => intros; rfl
        | cons h t ih => intros; simp [ih]
      have shift : ∀ (b : List Int) (init : Int),
        b.foldl (fun acc x => acc + x) init = init + b.foldl (fun acc x => acc + x) 0 := by
        intro b; induction b with
        | nil => intro init; simp
        | cons h t ih => intro init; simp only [List.foldl_cons]; rw [ih (init + h), ih (0 + h)]; omega
      rw [aux, shift]
    `,
  })

  law("every and some over bounded Integer[] arrays work", domain<Integer<1, 100>[]>(), xs => {
    expect(xs.every(x => x >= 1)).toBe(true)
    expect(xs.some(x => x < 1)).toBe(false)
  })

  law("FALSE: countPositive is always strictly positive", domain<bigint[]>(), xs => {
    expect(countPositive(xs)).toBeGreaterThan(0n)
  })

  law("FALSE: reversing a list leaves it unchanged", domain<bigint[]>(), xs => {
    expect(xs.toReversed()).toEqual(xs)
  })
})

describe("recursive functions", () => {
  law("sumToRec evaluates on small inputs and is non-negative for all bigints via induction", domain<bigint>(), n => {
    expect(sumToRec(n)).toBeGreaterThanOrEqual(0n)
  }, {
    proof: `
      induction x0 using sumToRec.induct with
      | case1 n h => unfold sumToRec; simp_all
      | case2 n h ih => unfold sumToRec; simp_all; omega
    `,
  })

  law("sumToRec matches closed form on small concrete inputs", domain<Integer<0, 10>>(), n => {
    expect(sumToRec(BigInt(n)) * 2n).toEqual(BigInt(n) * (BigInt(n) + 1n))
  })

  law("sumRec over arbitrary lists matches append via induction", domain<[bigint[], bigint[]]>(), ([xs, ys]) => {
    expect(sumRec(xs.concat(ys))).toEqual(sumRec(xs) + sumRec(ys))
  }, {
    proof: `
      simp only [beq_iff_eq]
      induction x0 with
      | nil => unfold sumRec; simp [_p_listLen]
      | cons h t ih =>
        simp only [List.cons_append]
        conv => lhs; unfold sumRec
        conv => rhs; arg 1; unfold sumRec
        simp [_p_listLen] at ih ⊢
        omega
    `,
  })

  law("FALSE: sumToRec is always strictly less than 10", domain<bigint>(), n => {
    expect(sumToRec(n)).toBeLessThan(10n)
  })

  law("SAMPLED: non-terminating recursion is refused by Lean termination checker", domain<bigint>(), n => {
    if (n >= 0n && n <= 10n) expect(nonTerminating(n)).toEqual(n)
  })
})
