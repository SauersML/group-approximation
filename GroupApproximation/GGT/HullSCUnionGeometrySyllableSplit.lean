import GroupApproximation.GGT.HullSCUnionGeometryTrichotomy

/-!
# The common prefix and the common suffix of two elements

The crossing estimate needs to know how much of a long `t` survives when `k`
displaces both endpoints of the segment from `1` to `t`.  This module supplies
the two splittings that answer it, and they replace the axis-distance invariant
the lineal branch was previously reduced to.

## The two splittings

`exists_common_prefix x y` writes `x = c * u` and `y = c * v` with the reduced
word of `x` the concatenation of those of `c` and `u`, likewise for `y`, and

    sylLength u + sylLength v ≤ sylLength (x⁻¹ * y) + 1 .

`exists_common_suffix x y` is the same read at `x⁻¹` and `y⁻¹`: it writes
`x = a * w` and `y = b * w` with

    sylLength a + sylLength b ≤ sylLength (y * x⁻¹) + 1 .

The `+ 1` is exactly one merged syllable, and it cannot be removed: `x` and `y`
may continue past their common prefix in the same factor with different letters,
and then the two leading syllables of `x⁻¹ * y` collapse into one.
`sylLength_branch_same` is that collapse, counted.

## Why the induction is on the prefix and not on a conjugator

The earlier route peeled the conjugator syllable by syllable and tried to
propagate a lower bound for `sylLength (g w g⁻¹)`.  No such bound holds: for `w`
cyclically reduced and `g = w ^ m` the conjugate is `w` again, so the conjugator
may be arbitrarily long without lengthening the conjugate at all.  The invariant
that would repair it is the distance from `g` to the axis of `w`, whose
definition already presupposes the conjugacy theorem.

Splitting `t` against `k * t` avoids all of it.  Both splittings are proved by a
single induction that peels the *shared* leading syllable, and each step is one
of three cases already available: the two words begin in different factors
(`sylLength_branch`), they begin in the same factor with different letters
(`sylLength_branch_same`), or they begin with the same syllable, which is the
recursive case.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.FreeProductCyclic

section SyllableSplit

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-! ## 1.  Syllable length at a branch -/

/-- The reduced word of the identity is empty. -/
theorem toList_equiv_one : (Word.equiv (1 : CoprodI G)).toList = [] := by
  rw [equiv_one]; rfl

/-- **Nothing cancels between words that begin in different factors**, counted in
syllables rather than in letters. -/
theorem sylLength_branch {x y : CoprodI G}
    (h : Word.fstIdx (Word.equiv x) ≠ Word.fstIdx (Word.equiv y)) :
    sylLength (x⁻¹ * y) = sylLength x + sylLength y := by
  have hl := toList_equiv_inv_mul_of_fstIdx_ne h
  simp only [sylLength, hl, List.length_append,
    CoprodIWordInverse.length_invList]

/-- **Exactly the two leading syllables merge** when both words begin in the same
factor with different letters. -/
theorem sylLength_branch_same {i : ι} {u v : G i} {x y : CoprodI G}
    (hx : lead x = some ⟨i, u⟩) (hy : lead y = some ⟨i, v⟩) (huv : u ≠ v) :
    sylLength (x⁻¹ * y) + 1 = sylLength x + sylLength y := by
  obtain ⟨x', hxeq, -, hx'idx, hxlist⟩ := exists_split_toList hx
  obtain ⟨y', hyeq, -, hy'idx, hylist⟩ := exists_split_toList hy
  have huv1 : (u⁻¹ * v : G i) ≠ 1 := fun h => huv (inv_mul_eq_one.mp h)
  have hofm : (CoprodI.of (u⁻¹ * v) : CoprodI G)
      = (CoprodI.of u)⁻¹ * CoprodI.of v := by
    rw [map_mul, map_inv]
  have hprod : x⁻¹ * y = x'⁻¹ * (CoprodI.of (u⁻¹ * v) * y') := by
    rw [hxeq, hyeq, hofm]
    group
  have hm : Word.fstIdx (Word.equiv (CoprodI.of (u⁻¹ * v) * y')) = some i :=
    fstIdx_of_mul huv1 hy'idx
  have hbr : sylLength (x'⁻¹ * (CoprodI.of (u⁻¹ * v) * y'))
      = sylLength x' + sylLength (CoprodI.of (u⁻¹ * v) * y') := by
    refine sylLength_branch ?_
    rw [hm]
    exact hx'idx
  have hmid : sylLength (CoprodI.of (u⁻¹ * v) * y') = sylLength y' + 1 := by
    simp only [sylLength, toList_equiv_of_mul huv1 hy'idx, List.length_cons]
  have hxl : sylLength x = sylLength x' + 1 := by
    simp only [sylLength, hxlist, List.length_cons]
  have hyl : sylLength y = sylLength y' + 1 := by
    simp only [sylLength, hylist, List.length_cons]
  rw [hprod, hbr, hmid, hxl, hyl]
  omega

/-- A concatenated splitting of the reduced word exhibits a syllable prefix. -/
theorem isSyllablePrefix_of_toList_append {x c u : CoprodI G}
    (h : (Word.equiv x).toList
      = (Word.equiv c).toList ++ (Word.equiv u).toList) :
    IsSyllablePrefix c x := by
  show (Word.equiv c).toList <+: (Word.equiv x).toList
  rw [h]
  exact List.prefix_append _ _

/-- A prefix block begins where the whole word begins, so it avoids the same
factor. -/
theorem fstIdx_of_append_ne {x c u : CoprodI G} {i : ι}
    (hlist : (Word.equiv x).toList
      = (Word.equiv c).toList ++ (Word.equiv u).toList)
    (h : Word.fstIdx (Word.equiv x) ≠ some i) :
    Word.fstIdx (Word.equiv c) ≠ some i := by
  by_cases hc : (Word.equiv c).toList = []
  · simp [Word.fstIdx, hc]
  · rw [← fstIdx_of_toList_append hlist hc]
    exact h

/-! ## 2.  The common prefix -/

/-- The splitting at the empty prefix, which is what the three non-recursive
cases of the induction produce. -/
private theorem common_prefix_of_no_merge (x y : CoprodI G)
    (h : sylLength x + sylLength y ≤ sylLength (x⁻¹ * y) + 1) :
    ∃ c u v : CoprodI G, x = c * u ∧ y = c * v ∧
      (Word.equiv x).toList
          = (Word.equiv c).toList ++ (Word.equiv u).toList ∧
      (Word.equiv y).toList
          = (Word.equiv c).toList ++ (Word.equiv v).toList ∧
      sylLength u + sylLength v ≤ sylLength (x⁻¹ * y) + 1 := by
  refine ⟨1, x, y, (one_mul x).symm, (one_mul y).symm, ?_, ?_, h⟩
  · rw [toList_equiv_one, List.nil_append]
  · rw [toList_equiv_one, List.nil_append]

private theorem exists_common_prefix_aux :
    ∀ (n : ℕ) (x y : CoprodI G), sylLength x ≤ n →
      ∃ c u v : CoprodI G, x = c * u ∧ y = c * v ∧
        (Word.equiv x).toList
            = (Word.equiv c).toList ++ (Word.equiv u).toList ∧
        (Word.equiv y).toList
            = (Word.equiv c).toList ++ (Word.equiv v).toList ∧
        sylLength u + sylLength v ≤ sylLength (x⁻¹ * y) + 1 := by
  intro n
  induction n with
  | zero =>
      intro x y hx
      have hx1 : x = 1 := sylLength_eq_zero_iff.mp (Nat.le_zero.mp hx)
      refine common_prefix_of_no_merge x y ?_
      have h1 : sylLength x = 0 := by rw [hx1]; exact sylLength_eq_zero_iff.mpr rfl
      have h2 : x⁻¹ * y = y := by rw [hx1, inv_one, one_mul]
      rw [h1, h2]
      omega
  | succ n ih =>
      intro x y hx
      by_cases hx1 : x = 1
      · refine common_prefix_of_no_merge x y ?_
        have h1 : sylLength x = 0 := by
          rw [hx1]; exact sylLength_eq_zero_iff.mpr rfl
        have h2 : x⁻¹ * y = y := by rw [hx1, inv_one, one_mul]
        rw [h1, h2]
        omega
      obtain ⟨i, α, hp⟩ : ∃ (i : ι) (α : G i), lead x = some ⟨i, α⟩ := by
        rcases hlx : lead x with _ | ⟨i, α⟩
        · exact absurd (lead_eq_none_iff.mp hlx) hx1
        · exact ⟨i, α, rfl⟩
      by_cases hidx : Word.fstIdx (Word.equiv x) = Word.fstIdx (Word.equiv y)
      · have hfy : Word.fstIdx (Word.equiv y) = some i := by
          rw [← hidx]; exact fstIdx_of_lead_some hp
        obtain ⟨β, hq⟩ := exists_lead_index hfy
        by_cases hab : α = β
        · rw [← hab] at hq
          obtain ⟨x', hxeq, hα1, hx'idx, hxlist⟩ := exists_split_toList hp
          obtain ⟨y', hyeq, -, -, hylist⟩ := exists_split_toList hq
          have hxlen : sylLength x' ≤ n := by
            have hstep : sylLength x = sylLength x' + 1 := by
              simp only [sylLength, hxlist, List.length_cons]
            omega
          obtain ⟨c', u, v, hxu, hyv, hxl, hyl, hbd⟩ := ih x' y' hxlen
          have hc'idx : Word.fstIdx (Word.equiv c') ≠ some i :=
            fstIdx_of_append_ne hxl hx'idx
          refine ⟨CoprodI.of α * c', u, v, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hxeq, hxu, mul_assoc]
          · rw [hyeq, hyv, mul_assoc]
          · rw [hxlist, toList_equiv_of_mul hα1 hc'idx, hxl, List.cons_append]
          · rw [hylist, toList_equiv_of_mul hα1 hc'idx, hyl, List.cons_append]
          · have hxy : x⁻¹ * y = x'⁻¹ * y' := by
              rw [hxeq, hyeq]
              group
            rw [hxy]
            exact hbd
        · refine common_prefix_of_no_merge x y ?_
          have hbranch := sylLength_branch_same hp hq hab
          omega
      · refine common_prefix_of_no_merge x y ?_
        rw [sylLength_branch hidx]
        omega

/-- **The common prefix.**  Every pair of elements splits at a common syllable
prefix past which the two words cost, together, at most one syllable more than
their distance. -/
theorem exists_common_prefix (x y : CoprodI G) :
    ∃ c u v : CoprodI G, x = c * u ∧ y = c * v ∧
      (Word.equiv x).toList
          = (Word.equiv c).toList ++ (Word.equiv u).toList ∧
      (Word.equiv y).toList
          = (Word.equiv c).toList ++ (Word.equiv v).toList ∧
      sylLength u + sylLength v ≤ sylLength (x⁻¹ * y) + 1 :=
  exists_common_prefix_aux (sylLength x) x y le_rfl

/-! ## 3.  The common suffix -/

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- Inversion reverses a concatenation. -/
theorem invList_append (l₁ l₂ : List (Σ i, G i)) :
    CoprodIWordInverse.invList (l₁ ++ l₂)
      = CoprodIWordInverse.invList l₂ ++ CoprodIWordInverse.invList l₁ := by
  simp [CoprodIWordInverse.invList]

/-- The reduced word of an inverse, as a list. -/
theorem toList_equiv_inv (x : CoprodI G) :
    (Word.equiv x⁻¹).toList
      = CoprodIWordInverse.invList (Word.equiv x).toList := by
  rw [CoprodIWordInverse.equiv_inv]; rfl

/-- **The common suffix**, which is `exists_common_prefix` read at the inverses:
the last syllable of `x` is the first syllable of `x⁻¹`, and `invList` carries
one concatenation to the other. -/
theorem exists_common_suffix (x y : CoprodI G) :
    ∃ w a b : CoprodI G, x = a * w ∧ y = b * w ∧
      (Word.equiv x).toList
          = (Word.equiv a).toList ++ (Word.equiv w).toList ∧
      (Word.equiv y).toList
          = (Word.equiv b).toList ++ (Word.equiv w).toList ∧
      sylLength a + sylLength b ≤ sylLength (y * x⁻¹) + 1 := by
  obtain ⟨c, u, v, hxu, hyv, hxl, hyl, hbd⟩ := exists_common_prefix x⁻¹ y⁻¹
  have hx : (Word.equiv x).toList
      = CoprodIWordInverse.invList ((Word.equiv x⁻¹).toList) := by
    have h := toList_equiv_inv x⁻¹
    rwa [inv_inv] at h
  have hy : (Word.equiv y).toList
      = CoprodIWordInverse.invList ((Word.equiv y⁻¹).toList) := by
    have h := toList_equiv_inv y⁻¹
    rwa [inv_inv] at h
  refine ⟨c⁻¹, u⁻¹, v⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_inv_rev, ← hxu, inv_inv]
  · rw [← mul_inv_rev, ← hyv, inv_inv]
  · rw [hx, hxl, invList_append, ← toList_equiv_inv, ← toList_equiv_inv]
  · rw [hy, hyl, invList_append, ← toList_equiv_inv, ← toList_equiv_inv]
  · have hswap : sylLength (y * x⁻¹) = sylLength (x * y⁻¹) := by
      rw [← sylLength_inv (x * y⁻¹), mul_inv_rev, inv_inv]
    have hxx : ((x⁻¹)⁻¹ * y⁻¹ : CoprodI G) = x * y⁻¹ := by rw [inv_inv]
    rw [hxx] at hbd
    rw [sylLength_inv, sylLength_inv, hswap]
    exact hbd

end SyllableSplit

end HullSCUnionGeometry
end GroupApproximation
