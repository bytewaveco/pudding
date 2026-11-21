import { describe, domain, expect, law, type Integer } from "@bytewaveco/pudding"
import { calleeB, callerA, countPositive, divergesOnPos, doubleAll, makeRecAdder, nonTerminating, positives, shadowSelf, sumList, sumRec, sumToRec, throwingRec } from "./lists.ts"

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

  law("SAMPLED: late termination rejection with skipped inputs is not reported as checked", domain<0n | 1n>(), n => {
    expect(divergesOnPos(n)).toEqual(0n)
  })

  law("recursive caller and callee are emitted in topological order", domain<Integer<0, 4>>(), n => {
    const b = BigInt(n)
    expect(callerA(b) >= calleeB(b)).toBe(true)
  })

  law("FALSE: recursive closures capturing different constants return equal results", () => {
    const a = makeRecAdder(1n)
    const b = makeRecAdder(2n)
    expect(a(1n)).toEqual(b(1n))
  })

  law("shadowed local function with the same name is not treated as recursive", domain<Integer<0, 100>>(), n => {
    expect(shadowSelf(n)).toEqual(n + 1)
  })

  law("vacuity check accepts a guard calling a recursive function", domain<Integer<0, 6>>(), n => {
    const b = BigInt(n)
    if (sumToRec(b) > 0n) expect(b > 0n).toBe(true)
  })

  law("SAMPLED: calling a throwing recursive function inside try is refused", domain<bigint>(), n => {
    if (n <= 10n) {
      let ok = true
      try {
        throwingRec(n)
      } catch {
        ok = n < 0n
      }
      expect(ok).toBe(true)
    }
  })
})

describe("list and soundness edge cases", () => {
  law("concat of fixed array with symbolic list flattens properly", domain<bigint[]>(), xs => {
    if (xs.length <= 1000000) expect([1n].concat(xs).length).toEqual(xs.length + 1)
  })

  law("FALSE: [1n].concat(xs) always has length 2", domain<bigint[]>(), xs => {
    expect([1n].concat(xs).length).toEqual(2)
  })

  law("SAMPLED: flat over a symbolic list element is refused", domain<bigint[]>(), xs => {
    expect([xs].flat().length).toEqual(xs.length)
  })

  law("SAMPLED: flatMap returning a symbolic list is refused", domain<bigint[]>(), xs => {
    expect([0].flatMap(() => xs).length).toEqual(xs.length)
  })

  law("Object.hasOwn on symbolic lists models length and index keys accurately", domain<bigint[]>(), xs => {
    expect(Object.hasOwn(xs, "length")).toBe(true)
    expect(Object.hasOwn(xs, "0")).toEqual(xs.length > 0)
    expect(Object.hasOwn(xs, "foo")).toBe(false)
  })

  law("FALSE: any two arbitrary arrays are equal", domain<[bigint[], bigint[]]>(), ([xs, ys]) => {
    expect(xs).toEqual(ys)
  })

  law("FALSE: integer array never includes a dyadic fraction", domain<[Integer<0, 10>[], Integer<0, 10>]>(), ([xs, n]) => {
    expect(xs.includes(n / 2)).toBe(false)
  })

  law("integer array includes exact dyadic fraction when divisible", domain<[Integer<0, 10>[], Integer<0, 10>]>(), ([xs, n]) => {
    if (n % 2 === 0 && xs.includes(n / 2)) expect(xs.length > 0).toBe(true)
  })

  law("SAMPLED: symbolic some with throwing callback inside try is refused", domain<bigint[]>(), xs => {
    const res = (() => {
      try {
        return xs.some(x => {
          if (x < 0n) throw new Error("neg")
          return x === 0n
        })
      } catch {
        return false
      }
    })()
    expect(typeof res).toBe("boolean")
  })

  law("FALSE: reassigning for-of let variable inside a branch leaks to other branches", domain<bigint[]>(), xs => {
    let total = 0n
    for (let x of xs) {
      if (x > 10n) x = 100n
      total += x
    }
    let expected = 0n
    for (const x of xs) expected += 100n
    expect(total).toEqual(expected)
  })

  law("SAMPLED: expect inside for-of over a symbolic list is refused", domain<bigint[]>(), xs => {
    for (const x of xs) expect(x === x).toBe(true)
  })
})
