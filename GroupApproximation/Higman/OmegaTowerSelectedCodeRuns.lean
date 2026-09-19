import GroupApproximation.Higman.OmegaTowerSelectedSignedFactors

/-!
# Nontrivial selected-code runs

A nonempty contiguous run in a reduced selected word evaluates nontrivially in
the full rank-three code factor.  This is the fact which prevents a maximal
right-factor run from disappearing during binary-syllable normalization,
including runs made entirely from the zero block.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- A nonempty reduced raw selected word remains nontrivial after evaluation
in the complete selected code. -/
theorem selectedAHom_mk_ne_one_of_isReduced
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    (hred : FreeGroup.IsReduced L) (hne : L ≠ []) :
    selectedAHom m B (FreeGroup.mk L) ≠ 1 := by
  intro hcode
  have hword : FreeGroup.mk L = 1 := by
    apply selectedAHom_injective m B
    simpa using hcode
  have hempty : (FreeGroup.mk L).toWord = [] :=
    FreeGroup.toWord_eq_nil_iff.mpr hword
  rw [FreeGroup.toWord_mk, hred.reduce_eq] at hempty
  exact hne hempty

/-- Every nonempty contiguous segment of the canonical selected spelling has
nontrivial full-code evaluation.  This is the exact form consumed by maximal
right-factor runs. -/
theorem selectedAHom_mk_ne_one_of_infix_toWord
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {S : List (SelectedBlock m B × Bool)}
    (hS : S <:+: v.toWord) (hne : S ≠ []) :
    selectedAHom m B (FreeGroup.mk S) ≠ 1 := by
  apply selectedAHom_mk_ne_one_of_isReduced _ hne
  obtain ⟨p, q, hpq⟩ := hS
  have hred : FreeGroup.IsReduced (p ++ S ++ q) := by
    rw [hpq]
    exact FreeGroup.isReduced_toWord
  exact (List.isChain_append.mp
    (List.isChain_append.mp hred).1).2.1

/-- The low-row encoding is injective on legal window blocks already before
it is included into the disjoint free alphabet. -/
theorem lowRowFactor_elt_injective_on_blockSet (m : ℕ) :
    Set.InjOn (fun beta : E => lowRowFactor m (elt beta)) (blockSet m) := by
  intro beta hbeta gamma hgamma hEq
  apply lowRowProjection_elt_injective_on_blockSet m hbeta hgamma
  rw [lowRowProjection_eq_leftFactor]
  simpa only [MonoidHom.comp_apply] using
    congrArg (FreeGroup.map (Sum.inl : LowIndex m → LowIndex m ⊕ Fin 3)) hEq

/-- A reduced positive-negative seam cannot cancel the merged row syllable. -/
theorem row_seam_ne_one_of_reduced_pos_neg
    {m : ℕ} {B : Set E} {beta gamma : SelectedBlock m B}
    {L : List (SelectedBlock m B × Bool)}
    (hred : FreeGroup.IsReduced ((beta, true) :: (gamma, false) :: L)) :
    (lowRowFactor m (elt (beta : E)))⁻¹ *
        lowRowFactor m (elt (gamma : E)) ≠ 1 := by
  intro hrow
  have hEq : lowRowFactor m (elt (beta : E)) =
      lowRowFactor m (elt (gamma : E)) := inv_mul_eq_one.mp hrow
  have hbeta : (beta : E) = (gamma : E) :=
    lowRowFactor_elt_injective_on_blockSet m beta.property.2 gamma.property.2 hEq
  have hletter : beta = gamma := Subtype.ext hbeta
  subst gamma
  simp [FreeGroup.IsReduced] at hred

/-- A reduced negative-positive seam cannot cancel the merged full-code
syllable. -/
theorem code_seam_ne_one_of_reduced_neg_pos
    {m : ℕ} {B : Set E} {beta gamma : SelectedBlock m B}
    {L : List (SelectedBlock m B × Bool)}
    (hred : FreeGroup.IsReduced ((beta, false) :: (gamma, true) :: L)) :
    (aElt (beta : E))⁻¹ * aElt (gamma : E) ≠ 1 := by
  intro hcode
  have hbeta : (beta : E) = (gamma : E) :=
    aElt_injective (inv_mul_eq_one.mp hcode)
  have hletter : beta = gamma := Subtype.ext hbeta
  subst gamma
  simp [FreeGroup.IsReduced] at hred

end Omega
end Higman
end GroupApproximation
