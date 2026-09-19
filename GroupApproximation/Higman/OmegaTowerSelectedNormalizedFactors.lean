import GroupApproximation.Algebra.BinarySyllableNormalizer
import GroupApproximation.Higman.OmegaTowerSelectedSignedFactors

/-!
# Normalized binary syllables of a selected Omega word

This specializes the binary syllable normalizer to the raw signed-factor list
of a selected word.  The result is an actual `CoprodI.Word`, so its list has
nontrivial letters and alternating row/code indices by construction, while its
product is definitionally the complete selected link evaluation.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open Monoid Monoid.CoprodI
open BinarySyllableNormalizer

def indexedFactorToSyllable (m : ℕ) :
    (Σ i, LowStableFactor m i) →
      Syllable (FreeGroup (LowIndex m)) F₃
  | ⟨false, x⟩ => .row x
  | ⟨true, x⟩ => .code x

noncomputable def selectedSyllableList (m : ℕ) {B : Set E}
    (L : List (SelectedBlock m B × Bool)) :
    List (Syllable (FreeGroup (LowIndex m)) F₃) :=
  (selectedFactorList m L).map (indexedFactorToSyllable m)

theorem selectedSyllableList_cons_pos_ne_zero
    (m : ℕ) {B : Set E} (beta : SelectedBlock m B)
    (L : List (SelectedBlock m B × Bool)) (hbeta : (beta : E) ≠ 0) :
    selectedSyllableList m ((beta, true) :: L) =
      [.code (aElt (beta : E)),
        .row ((lowRowFactor m (elt (beta : E)))⁻¹)] ++
          selectedSyllableList m L := by
  simp [selectedSyllableList, selectedFactorList, selectedSignedFactors,
    indexedFactorToSyllable, hbeta]

theorem selectedSyllableList_cons_neg_ne_zero
    (m : ℕ) {B : Set E} (beta : SelectedBlock m B)
    (L : List (SelectedBlock m B × Bool)) (hbeta : (beta : E) ≠ 0) :
    selectedSyllableList m ((beta, false) :: L) =
      [.row (lowRowFactor m (elt (beta : E))),
        .code ((aElt (beta : E))⁻¹)] ++ selectedSyllableList m L := by
  simp [selectedSyllableList, selectedFactorList, selectedSignedFactors,
    indexedFactorToSyllable, hbeta]

theorem selectedSyllableList_cons_zero
    (m : ℕ) {B : Set E} (beta : SelectedBlock m B)
    (L : List (SelectedBlock m B × Bool)) (hbeta : (beta : E) = 0)
    (s : Bool) :
    selectedSyllableList m ((beta, s) :: L) =
      [.code (if s then aElt (beta : E) else (aElt (beta : E))⁻¹)] ++
        selectedSyllableList m L := by
  cases s <;>
    simp [selectedSyllableList, selectedFactorList, selectedSignedFactors,
      indexedFactorToSyllable, hbeta]

theorem evalList_selectedSyllableList
    (m : ℕ) {B : Set E} (L : List (SelectedBlock m B × Bool)) :
    evalList (selectedSyllableList m L) =
      CoprodIAltWord.listProd (selectedFactorList m L) := by
  unfold selectedSyllableList evalList CoprodIAltWord.listProd
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨i, x⟩
  cases i <;> rfl

noncomputable def selectedNormalizedWord (m : ℕ) {B : Set E}
    (v : FreeGroup (SelectedBlock m B)) :
    CoprodI.Word (Factor (FreeGroup (LowIndex m)) F₃) :=
  normalizedWord (selectedSyllableList m v.toWord)

/-- The normalized binary word evaluates to the complete selected link word. -/
theorem selectedNormalizedWord_prod
    (m : ℕ) {B : Set E} (v : FreeGroup (SelectedBlock m B)) :
    (selectedNormalizedWord m v).prod = selectedIndexedLinkHom m B v := by
  rw [selectedNormalizedWord, normalizedWord_prod,
    evalList_selectedSyllableList, listProd_selectedFactorList_toWord]

/-- The normal form of the three-factor returning right-hand side has at most
three syllables, including all degeneracies where an endpoint or the middle
code is trivial. -/
theorem selectedNormalizedWord_length_le_three_of_equation
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)} {l f : E}
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) (lowRowFactor m (elt l)) *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) (lowRowFactor m (elt f)))⁻¹) :
    (selectedNormalizedWord m v).toList.length ≤ 3 := by
  classical
  let rhs : List (Syllable (FreeGroup (LowIndex m)) F₃) :=
    [.row (lowRowFactor m (elt l)),
      .code (selectedAHom m B v),
      .row ((lowRowFactor m (elt f))⁻¹)]
  have hrhs : evalList rhs =
      CoprodI.of (i := false) (lowRowFactor m (elt l)) *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) (lowRowFactor m (elt f)))⁻¹ := by
    simp [rhs, evalList, eval, mul_assoc]
  have hprod : (selectedNormalizedWord m v).prod =
      (normalizedWord rhs).prod := by
    rw [selectedNormalizedWord_prod, normalizedWord_prod, hrhs, hEq]
  have hword : selectedNormalizedWord m v = normalizedWord rhs := by
    apply CoprodI.Word.equiv.symm.injective
    exact hprod
  rw [hword]
  change ((normalize rhs).map Syllable.toSigma).length ≤ 3
  rw [List.length_map]
  exact le_trans (length_normalize_le rhs) (by simp [rhs])

@[simp] theorem selectedNormalizedWord_toList
    (m : ℕ) {B : Set E} (v : FreeGroup (SelectedBlock m B)) :
    (selectedNormalizedWord m v).toList =
      (normalize (selectedSyllableList m v.toWord)).map Syllable.toSigma := rfl

end Omega
end Higman
end GroupApproximation
