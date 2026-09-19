import GroupApproximation.Higman.OmegaTowerIndexCanonicalThree
import GroupApproximation.Higman.OmegaTowerLowStableIndexed
import GroupApproximation.Higman.OmegaTowerSelectedOrbitWord

/-!
# The returning selected-word equation in a binary indexed free product

The canonical index-row tower embeds in the concrete three-stage row tower,
so the full link equation can be reflected into it without losing any code
generator.  Projecting afterward gives an equality in the free product of
the low row group and the complete rank-three code group.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open Monoid Monoid.CoprodI

noncomputable def selectedIndexCodeHom (m : ℕ) (B : Set E) :
    FreeGroup (SelectedBlock m B) →* IndexCent3 m :=
  (indexGenHom m).comp (selectedAHom m B)

noncomputable def selectedIndexLinkHom (m : ℕ) (B : Set E) :
    FreeGroup (SelectedBlock m B) →* IndexCent3 m :=
  FreeGroup.lift fun beta => indexLinkElem m (beta : E)

@[simp] theorem selectedIndexCodeHom_of
    (m : ℕ) (B : Set E) (beta : SelectedBlock m B) :
    selectedIndexCodeHom m B (FreeGroup.of beta) =
      indexGenCode m (beta : E) := by
  simp [selectedIndexCodeHom, indexGenCode]

@[simp] theorem selectedIndexLinkHom_of
    (m : ℕ) (B : Set E) (beta : SelectedBlock m B) :
    selectedIndexLinkHom m B (FreeGroup.of beta) =
      indexLinkElem m (beta : E) := by
  simp [selectedIndexLinkHom]

theorem indexCanonical3_comp_selectedIndexCodeHom
    (m : ℕ) (B : Set E) :
    (indexCanonical3 m).comp (selectedIndexCodeHom m B) =
      selectedCodeHom m B := by
  refine FreeGroup.ext_hom _ _ fun beta => ?_
  simp only [MonoidHom.comp_apply, selectedIndexCodeHom_of,
    indexCanonical3_indexGenCode, selectedCodeHom_of]

theorem indexCanonical3_comp_selectedIndexLinkHom
    (m : ℕ) (B : Set E) :
    (indexCanonical3 m).comp (selectedIndexLinkHom m B) =
      selectedLinkHom m B := by
  refine FreeGroup.ext_hom _ _ fun beta => ?_
  simp only [MonoidHom.comp_apply, selectedIndexLinkHom_of,
    indexCanonical3_indexLinkElem]
  simp [selectedLinkHom, slimLinkLift, selectedBlockIncl]

/-- Reflect the complete returning equation into the index-row tower. -/
theorem selectedIndexLinkHom_eq_of_returning
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)} {l f : E}
    (hv : selectedLinkHom m B v =
      slimBaseCode m l * selectedCodeHom m B v *
        (slimBaseCode m f)⁻¹) :
    selectedIndexLinkHom m B v =
      indexBaseCode m l * selectedIndexCodeHom m B v *
        (indexBaseCode m f)⁻¹ := by
  apply indexCanonical3_injective m
  rw [← MonoidHom.comp_apply,
    indexCanonical3_comp_selectedIndexLinkHom,
    map_mul, map_mul, map_inv,
    indexCanonical3_indexBaseCode,
    ← MonoidHom.comp_apply,
    indexCanonical3_comp_selectedIndexCodeHom,
    indexCanonical3_indexBaseCode]
  exact hv

/-- Evaluation of the selected link word in the indexed free product. -/
noncomputable def selectedIndexedLinkHom (m : ℕ) (B : Set E) :
    FreeGroup (SelectedBlock m B) →* LowStableIndexed m :=
  (lowStableToIndexed m).comp
    ((lowStableProjection3 m).comp (selectedIndexLinkHom m B))

@[simp] theorem selectedIndexedLinkHom_of
    (m : ℕ) (B : Set E) (beta : SelectedBlock m B) :
    selectedIndexedLinkHom m B (FreeGroup.of beta) =
      CoprodI.of (i := true) (aElt (beta : E)) *
        (CoprodI.of (i := false)
          (lowRowFactor m (elt (beta : E))))⁻¹ := by
  simp [selectedIndexedLinkHom]

/-- Exact full-code free-product equation attached to a returning Omega orbit
label. -/
theorem exists_selected_indexed_equation_of_rightLabel_rowLabel_eq
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l f : E}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f)) :
    ∃ v : FreeGroup (SelectedBlock m B),
      selectedIndexedLinkHom m B v =
        CoprodI.of (i := false) (lowRowFactor m (elt l)) *
          CoprodI.of (i := true) (selectedAHom m B v) *
            (CoprodI.of (i := false) (lowRowFactor m (elt f)))⁻¹ := by
  obtain ⟨v, hvCode, hvLink, _hvRow⟩ :=
    exists_selected_orbit_word_of_rightLabel_rowLabel_eq hg hlabel
  refine ⟨v, ?_⟩
  have hvLink' : selectedLinkHom m B v =
      slimBaseCode m l * selectedCodeHom m B v *
        (slimBaseCode m f)⁻¹ := by
    rw [hvCode]
    exact hvLink
  have hindex := selectedIndexLinkHom_eq_of_returning hvLink'
  have hproject := congrArg
    ((lowStableToIndexed m).comp (lowStableProjection3 m)) hindex
  change selectedIndexedLinkHom m B v = _ at hproject
  have hcode : lowStableToIndexed m
      (lowStableProjection3 m
        (indexGenHom m (selectedAHom m B v))) =
      CoprodI.of (i := true) (selectedAHom m B v) := by
    change lowStableToIndexed m
      (((lowStableProjection3 m).comp (indexGenHom m))
        (selectedAHom m B v)) = _
    rw [lowStableProjection3_comp_genHom,
      lowStableToIndexed_stableFreeHom]
  simpa only [map_mul, map_inv, lowStableProjection3_indexBaseCode,
    lowStableToIndexed_lowRowProjection, selectedIndexCodeHom,
    MonoidHom.comp_apply, hcode] using hproject

end Omega
end Higman
end GroupApproximation
