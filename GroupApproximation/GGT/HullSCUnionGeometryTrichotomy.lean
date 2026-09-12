import GroupApproximation.GGT.HullSCUnionGeometryCyclic

/-!
# The peel trichotomy, first case

The conjugacy theorem is proved by peeling the last syllable of the conjugator:
`g s g⁻¹ = g₁ · ((of z) · s · (of z)⁻¹) · g₁⁻¹`.  What the induction needs is a
trichotomy for the inner conjugation, according to the factor `p` of `z`
against the first factor `i` and the last factor `j` of the cyclically reduced
`s`:

* `p ∉ {i, j}` --- nothing cancels at either seam, the word grows by two
  syllables, and cyclic reducedness is destroyed (both ends now lie in `p`);
* `p = i` and `z` does not invert the leading syllable --- the two merge, the
  word grows by one, and again both ends lie in `i`;
* `p = i` and `z` *does* invert it --- the cyclic permutation of
  `exists_cyclicPermute`, which preserves both the syllable count and cyclic
  reducedness;

and the mirror of the last two at `p = j`, obtained by reading the first three
at `s⁻¹`.

This module proves the first case, `conj_single_of_fstIdx_ne`, in the form the
induction consumes: the exact syllable count *and* the first index of the
result.  `not_isCyclicallyReduced_conj_single` is then immediate, because the
first index of the inverse is computed by the same lemma read at `s⁻¹`
(`IsCyclicallyReduced.inv`), and the two agree.

## What the induction still needs

The remaining cases, and then the propagation step: knowing that one peel
lengthens `s` is not yet knowing that `g₁` cannot shorten it again.  The
invariant that closes that is a lower bound of the shape

    sylLength (h w h⁻¹) ≥ sylLength w - 2 · (syllables of h that cancel) ,

i.e. the distance from `h` to the axis of `s`, and it is the one piece of this
argument that the seam lemmas do not already give.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.FreeProductCyclic

section Trichotomy

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- A cyclically reduced word is nontrivial. -/
theorem ne_one_of_isCyclicallyReduced {s : CoprodI G}
    (hcr : IsCyclicallyReduced s) : s ≠ 1 := by
  intro hs
  exact hcr (by rw [hs, inv_one])

/-- **Case A: no seam.**  Conjugating a cyclically reduced word by a syllable in
a factor it neither begins nor ends in lengthens it by exactly two syllables,
and the result begins in that factor. -/
theorem conj_single_of_fstIdx_ne {s : CoprodI G} (hcr : IsCyclicallyReduced s)
    {p : ι} {z : G p} (hz : z ≠ 1)
    (h1 : Word.fstIdx (Word.equiv s) ≠ some p)
    (h2 : Word.fstIdx (Word.equiv s⁻¹) ≠ some p) :
    sylLength (CoprodI.of z * s * (CoprodI.of z)⁻¹) = sylLength s + 2 ∧
      Word.fstIdx (Word.equiv (CoprodI.of z * s * (CoprodI.of z)⁻¹))
        = some p := by
  have hzinv : ((CoprodI.of z : CoprodI G)⁻¹) = CoprodI.of z⁻¹ :=
    (map_inv (CoprodI.of : G p →* CoprodI G) z).symm
  have hz1 : Word.fstIdx (Word.equiv (CoprodI.of z : CoprodI G)) = some p :=
    fstIdx_of_single hz
  have hz2 : Word.fstIdx (Word.equiv ((CoprodI.of z : CoprodI G)⁻¹)) = some p := by
    rw [hzinv]
    exact fstIdx_of_single (inv_ne_one.mpr hz)
  have hzt : (Word.equiv ((CoprodI.of z : CoprodI G)⁻¹)).toList = [⟨p, z⁻¹⟩] := by
    rw [hzinv]
    exact toList_equiv_of_single (inv_ne_one.mpr hz)
  have hA : (Word.equiv (CoprodI.of z * s)).toList
      = (Word.equiv (CoprodI.of z : CoprodI G)).toList
        ++ (Word.equiv s).toList := by
    refine toList_equiv_mul_of_seam ?_
    rw [hz2]
    exact fun hcon => h1 hcon.symm
  have hB : Word.fstIdx (Word.equiv (CoprodI.of z * s)⁻¹)
      = Word.fstIdx (Word.equiv s⁻¹) := by
    have hrw : ((CoprodI.of z * s)⁻¹ : CoprodI G) = s⁻¹ * CoprodI.of z⁻¹ := by
      rw [mul_inv_rev, hzinv]
    rw [hrw]
    refine fstIdx_equiv_inv_mul (ne_one_of_isCyclicallyReduced hcr) ?_
    rw [fstIdx_of_single (inv_ne_one.mpr hz)]
    exact h1
  have hC : (Word.equiv (CoprodI.of z * s * (CoprodI.of z)⁻¹)).toList
      = (Word.equiv (CoprodI.of z * s)).toList
        ++ (Word.equiv ((CoprodI.of z : CoprodI G)⁻¹)).toList := by
    refine toList_equiv_mul_of_seam ?_
    rw [hB, hz2]
    exact h2
  have hnez : (Word.equiv (CoprodI.of z : CoprodI G)).toList ≠ [] := by
    rw [toList_equiv_of_single hz]
    simp
  have hne1 : (Word.equiv (CoprodI.of z * s)).toList ≠ [] := by
    rw [hA]
    simp [toList_equiv_of_single hz]
  constructor
  · simp only [sylLength, hC, hA, toList_equiv_of_single hz, hzt,
      List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [fstIdx_of_toList_append hC hne1, fstIdx_of_toList_append hA hnez, hz1]

/-- **Case A destroys cyclic reducedness.**  Both ends of the result lie in the
factor of `z`: the first index of the inverse is the same lemma read at `s⁻¹`. -/
theorem not_isCyclicallyReduced_conj_single {s : CoprodI G}
    (hcr : IsCyclicallyReduced s) {p : ι} {z : G p} (hz : z ≠ 1)
    (h1 : Word.fstIdx (Word.equiv s) ≠ some p)
    (h2 : Word.fstIdx (Word.equiv s⁻¹) ≠ some p) :
    ¬ IsCyclicallyReduced (CoprodI.of z * s * (CoprodI.of z)⁻¹) := by
  intro hcon
  refine hcon ?_
  have hrw : ((CoprodI.of z * s * (CoprodI.of z)⁻¹)⁻¹ : CoprodI G)
      = CoprodI.of z * s⁻¹ * (CoprodI.of z)⁻¹ := by group
  rw [(conj_single_of_fstIdx_ne hcr hz h1 h2).2, hrw,
    (conj_single_of_fstIdx_ne hcr.inv hz h2 (by rw [inv_inv]; exact h1)).2]

end Trichotomy

end HullSCUnionGeometry
end GroupApproximation
