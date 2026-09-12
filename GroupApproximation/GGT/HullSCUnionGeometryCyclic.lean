import GroupApproximation.GGT.HullSCUnionGeometryFactorBranch

/-!
# Cyclically reduced words, and the cyclic permutation peel

The lineal branch of the crossing estimate needs the free-product conjugacy
theorem for cyclically reduced words.  This module is its combinatorial core:
the definition, and the one move the induction is built from.

## Cyclically reduced, without `NeWord`

`IsCyclicallyReduced s` says the first and last syllables of `s` lie in different
factors --- and the last syllable of `s` is the first syllable of `s⁻¹`, so the
whole condition is

    Word.fstIdx s‾ ≠ Word.fstIdx (s⁻¹)‾ .

Nothing else is needed: this already forces two syllables (`ne_one_of_split`
below is the one-syllable case, where first and last coincide), it is visibly
invariant under inversion, and it is stated in exactly the vocabulary the seam
lemmas consume.  `Monoid.CoprodI.NeWord`, which
`FreeProductCyclic.exists_cyclicReduction` uses, is never mentioned.

## The peel

`exists_cyclicPermute` moves the leading syllable `a` of `s` to the back:

    (of a)⁻¹ · s · (of a)  =  v · (of a) ,      s = (of a) · v ,

and the result is again cyclically reduced with the *same* syllable count.  Both
halves come from the seam lemmas rather than from any list surgery: `v`'s last
syllable is `s`'s last syllable --- read off by `fstIdx_equiv_inv_mul` applied to
`s⁻¹ = v⁻¹ · (of a⁻¹)` --- so it avoids the factor of `a`, which is exactly the
seam condition for `v · (of a)`.

This is the move that a conjugator can perform for free, and the conjugacy
theorem is the statement that it is the *only* one: peeling the last syllable of
`g` in `g s g⁻¹` either performs a cyclic permutation, or lengthens the word.
The length trichotomy for the other cases, and the induction on `sylLength g`
that it feeds, are the next step.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.FreeProductCyclic

section Cyclic

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- **Cyclically reduced**: the first syllable and the last lie in different
factors.  The last syllable of `s` is the first syllable of `s⁻¹`. -/
def IsCyclicallyReduced (s : CoprodI G) : Prop :=
  Word.fstIdx (Word.equiv s) ≠ Word.fstIdx (Word.equiv s⁻¹)

theorem IsCyclicallyReduced.inv {s : CoprodI G} (h : IsCyclicallyReduced s) :
    IsCyclicallyReduced s⁻¹ := by
  intro hcon
  rw [inv_inv] at hcon
  exact h hcon.symm

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The first index of a word whose reduced form starts with a nonempty block. -/
theorem fstIdx_of_toList_append {w w' : Word G} {l : List (Σ i, G i)}
    (h : w.toList = w'.toList ++ l) (hne : w'.toList ≠ []) :
    Word.fstIdx w = Word.fstIdx w' := by
  obtain ⟨p, l', hp⟩ := List.exists_cons_of_ne_nil hne
  simp only [Word.fstIdx, h, hp, List.cons_append, List.head?_cons]

theorem toList_ne_nil_of_ne_one {v : CoprodI G} (hv : v ≠ 1) :
    (Word.equiv v).toList ≠ [] := by
  intro hnil
  exact hv (sylLength_eq_zero_iff.mp (by simp [sylLength, hnil]))

/-- **The tail of a cyclically reduced word is nontrivial.**  A single syllable
has its first and its last syllable in the same factor, so it is never cyclically
reduced. -/
theorem ne_one_of_split {s v : CoprodI G} (hcr : IsCyclicallyReduced s) {i : ι}
    {a : G i} (ha1 : a ≠ 1) (hseq : s = CoprodI.of a * v) : v ≠ 1 := by
  intro hv
  have hsa : s = CoprodI.of a := by rw [hseq, hv, mul_one]
  have hainv : ((CoprodI.of a : CoprodI G)⁻¹) = CoprodI.of a⁻¹ :=
    (map_inv (CoprodI.of : G i →* CoprodI G) a).symm
  refine hcr ?_
  rw [hsa, fstIdx_of_single ha1, hainv, fstIdx_of_single (inv_ne_one.mpr ha1)]

/-- **The cyclic permutation peel.**  Moving the leading syllable of a cyclically
reduced word to the back is a conjugation, and the result is again cyclically
reduced with the same syllable count. -/
theorem exists_cyclicPermute {s : CoprodI G} (hcr : IsCyclicallyReduced s)
    {i : ι} {a : G i} (hlead : lead s = some ⟨i, a⟩) :
    ∃ v : CoprodI G, s = CoprodI.of a * v ∧
      (CoprodI.of a)⁻¹ * s * CoprodI.of a = v * CoprodI.of a ∧
      IsCyclicallyReduced (v * CoprodI.of a) ∧
      sylLength (v * CoprodI.of a) = sylLength s := by
  obtain ⟨v, hseq, ha1, hvidx, hlist⟩ := exists_split_toList hlead
  have hfa : Word.fstIdx (Word.equiv (CoprodI.of a : CoprodI G)) = some i :=
    fstIdx_of_single ha1
  have hv1 : v ≠ 1 := ne_one_of_split hcr ha1 hseq
  have hlvne : (Word.equiv v).toList ≠ [] := toList_ne_nil_of_ne_one hv1
  -- the last syllable of `s` is the last syllable of `v`
  have hsinv : (s : CoprodI G)⁻¹ = v⁻¹ * CoprodI.of a⁻¹ := by
    rw [hseq, mul_inv_rev, ← map_inv]
  have hfs : Word.fstIdx (Word.equiv s⁻¹) = Word.fstIdx (Word.equiv v⁻¹) := by
    rw [hsinv]
    refine fstIdx_equiv_inv_mul hv1 ?_
    rw [fstIdx_of_single (inv_ne_one.mpr ha1)]
    exact hvidx
  have hlast : Word.fstIdx (Word.equiv v⁻¹) ≠ some i := by
    rw [← hfs]
    intro hcon
    exact hcr (by rw [fstIdx_of_lead_some hlead, hcon])
  -- the peel is seam-free
  have hcat : (Word.equiv (v * CoprodI.of a)).toList
      = (Word.equiv v).toList
        ++ (Word.equiv (CoprodI.of a : CoprodI G)).toList := by
    refine toList_equiv_mul_of_seam ?_
    rw [hfa]
    exact hlast
  have hfvca : Word.fstIdx (Word.equiv (v * CoprodI.of a))
      = Word.fstIdx (Word.equiv v) :=
    fstIdx_of_toList_append hcat hlvne
  have hinvca : Word.fstIdx (Word.equiv (v * CoprodI.of a)⁻¹) = some i := by
    have hrw : ((v * CoprodI.of a)⁻¹ : CoprodI G) = CoprodI.of a⁻¹ * v⁻¹ := by
      rw [mul_inv_rev, ← map_inv]
    rw [hrw]
    exact fstIdx_of_mul (inv_ne_one.mpr ha1) hlast
  refine ⟨v, hseq, ?_, ?_, ?_⟩
  · rw [hseq]
    group
  · rw [IsCyclicallyReduced, hfvca, hinvca]
    exact hvidx
  · rw [sylLength, sylLength, hcat, hlist, toList_equiv_of_single ha1,
      List.length_append, List.length_cons]
    simp

end Cyclic

end HullSCUnionGeometry
end GroupApproximation
