import GroupApproximation.Higman.OmegaTowerSelectedIndexedEquation
import GroupApproximation.Higman.OmegaTowerRightTailSubgroup

/-!
# Signed-factor expansion of a selected Omega word

Every positive selected letter contributes a code syllable followed by an
inverse row syllable; every negative letter contributes a row syllable
followed by an inverse code syllable.  For the zero block the row syllable is
literally trivial and is omitted, while its genuine code syllable is retained.
This is the raw list that the final maximal-run normalization must compress.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq
open Monoid Monoid.CoprodI

/-- The factor syllables contributed by one signed selected letter.  `true`
is the positive free-group letter and `false` is its inverse. -/
noncomputable def selectedSignedFactors (m : ℕ) {B : Set E}
    (p : SelectedBlock m B × Bool) :
    List (Σ i, LowStableFactor m i) :=
  if p.2 then
    if _hbeta : (p.1 : E) = 0 then
      [⟨true, aElt (p.1 : E)⟩]
    else
      [⟨true, aElt (p.1 : E)⟩,
        ⟨false, (lowRowFactor m (elt (p.1 : E)))⁻¹⟩]
  else
    if _hbeta : (p.1 : E) = 0 then
      [⟨true, (aElt (p.1 : E))⁻¹⟩]
    else
      [⟨false, lowRowFactor m (elt (p.1 : E))⟩,
        ⟨true, (aElt (p.1 : E))⁻¹⟩]

/-- Concatenate the signed-factor expansions of a raw selected word. -/
noncomputable def selectedFactorList (m : ℕ) {B : Set E}
    (L : List (SelectedBlock m B × Bool)) :
    List (Σ i, LowStableFactor m i) :=
  L.flatMap (selectedSignedFactors m)

theorem listProd_append_selectedFactors
    (m : ℕ) (L₁ L₂ : List (Σ i, LowStableFactor m i)) :
    CoprodIAltWord.listProd (L₁ ++ L₂) =
      CoprodIAltWord.listProd L₁ * CoprodIAltWord.listProd L₂ := by
  simp [CoprodIAltWord.listProd]

/-- One signed letter has exactly the advertised complete link evaluation. -/
theorem listProd_selectedSignedFactors
    (m : ℕ) {B : Set E} (p : SelectedBlock m B × Bool) :
    CoprodIAltWord.listProd (selectedSignedFactors m p) =
      selectedIndexedLinkHom m B (FreeGroup.mk [p]) := by
  rcases p with ⟨beta, s⟩
  cases s with
  | false =>
      have hmk : FreeGroup.mk [(beta, false)] =
          (FreeGroup.of beta)⁻¹ := by
        show FreeGroup.mk [(beta, false)] =
          (FreeGroup.mk [(beta, true)])⁻¹
        rw [FreeGroup.inv_mk]
        rfl
      rw [hmk, map_inv, selectedIndexedLinkHom_of]
      by_cases hbeta : (beta : E) = 0
      · simp [selectedSignedFactors, hbeta, CoprodIAltWord.listProd]
      · simp [selectedSignedFactors, hbeta, CoprodIAltWord.listProd]
  | true =>
      have hmk : FreeGroup.mk [(beta, true)] = FreeGroup.of beta := rfl
      rw [hmk, selectedIndexedLinkHom_of]
      by_cases hbeta : (beta : E) = 0
      · simp [selectedSignedFactors, hbeta, CoprodIAltWord.listProd]
      · simp [selectedSignedFactors, hbeta, CoprodIAltWord.listProd]

/-- Evaluation of the raw factor list agrees with evaluation of the raw free
word. -/
theorem listProd_selectedFactorList
    (m : ℕ) {B : Set E} (L : List (SelectedBlock m B × Bool)) :
    CoprodIAltWord.listProd (selectedFactorList m L) =
      selectedIndexedLinkHom m B (FreeGroup.mk L) := by
  induction L with
  | nil =>
      change 1 = selectedIndexedLinkHom m B 1
      rw [map_one]
  | cons p L ih =>
      change CoprodIAltWord.listProd
          (selectedSignedFactors m p ++ selectedFactorList m L) = _
      rw [listProd_append_selectedFactors,
        listProd_selectedSignedFactors, ih]
      change _ = selectedIndexedLinkHom m B
        (FreeGroup.mk [p] * FreeGroup.mk L)
      rw [map_mul]

/-- The signed-factor list of the canonical reduced spelling evaluates to the
original selected link word. -/
theorem listProd_selectedFactorList_toWord
    (m : ℕ) {B : Set E} (v : FreeGroup (SelectedBlock m B)) :
    CoprodIAltWord.listProd (selectedFactorList m v.toWord) =
      selectedIndexedLinkHom m B v := by
  rw [listProd_selectedFactorList, FreeGroup.mk_toWord]

/-- A nonzero legal block has a nontrivial low-row factor. -/
theorem lowRowFactor_elt_ne_one_of_ne_zero
    {m : ℕ} {beta : E} (hblock : beta ∈ blockSet m) (hbeta : beta ≠ 0) :
    lowRowFactor m (elt beta) ≠ 1 := by
  intro hrow
  have hproj : lowRowProjection m (elt beta) = 1 := by
    rw [lowRowProjection_eq_leftFactor, MonoidHom.comp_apply, hrow, map_one]
  have helt : elt beta = 1 := by
    rw [← lowStableRowRetraction_lowRowProjection_elt hblock, hproj, map_one]
  apply hbeta
  apply elt_injective
  simpa using helt

/-- The low-row factor is trivial exactly for a sequence supported in the
right tail.  This identifies the endpoint degeneracies in the three-syllable
returning normal form with the sequence predicate used by
`CanonicalReturnRelation`. -/
theorem lowRowFactor_elt_eq_one_iff_rightTailSet (m : ℕ) (l : E) :
    lowRowFactor m (elt l) = 1 ↔ rightTailSet m l := by
  constructor
  · intro hlow i hi
    have hproj : lowRowProjection m (elt l) = 1 := by
      rw [lowRowProjection_eq_leftFactor, MonoidHom.comp_apply, hlow, map_one]
    have hkill : Split.killOn (fun j : ℤ => j < (m : ℤ)) (elt l) = 1 := by
      rw [← lowStableRowRetraction_comp_lowRowProjection,
        MonoidHom.comp_apply, hproj, map_one]
    rw [Split.killOn_elt] at hkill
    have hfilter : Finsupp.filter (fun j : ℤ => j < (m : ℤ)) l = 0 := by
      apply elt_injective
      simpa using hkill
    by_contra him
    have hilow : i < (m : ℤ) := lt_of_not_ge him
    have hi0 := congrArg (fun f : E => f i) hfilter
    simp [hilow, hi] at hi0
  · intro htail
    have hmem : elt l ∈ tailIndexSub m := by
      unfold tailIndexSub RowDeletionGraph.indexSub
      apply Split.elt_mem_closure
      intro i hi
      exact htail i (Finsupp.mem_support_iff.mp hi)
    have hproj := lowRowProjection_eq_one_of_mem_tailIndexSub hmem
    rw [lowRowProjection_eq_leftFactor, MonoidHom.comp_apply] at hproj
    have hinj : Function.Injective (FreeGroup.map (Sum.inl : LowIndex m →
        LowIndex m ⊕ Fin 3)) :=
      FreeGroup.map_injective Sum.inl_injective
    apply hinj
    simpa using hproj

end Omega
end Higman
end GroupApproximation
