import GroupApproximation.Higman.OmegaTowerSelectedEndpointTags
import GroupApproximation.Higman.OmegaTowerSelectedLengthInduction

/-!
# Endpoint factors without a canonical target sequence

For the static-seam orbit intersection the returning row label initially has
an arbitrary `K` index.  Its retained low-row word is nevertheless the right
factor in the same binary free-product normal form.  These lemmas expose the
endpoint tag and value comparisons using arbitrary low-row factors.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq
open GroupApproximation.Higman.Conj (F₃)
open BinarySyllableNormalizer
open Monoid Monoid.CoprodI

universe u

theorem syllableToSigma_injective
    {L R : Type u} [Group L] [Group R] :
    Function.Injective (Syllable.toSigma : Syllable L R → Σ i, Factor L R i) := by
  intro x y hxy
  cases x with
  | row a =>
      cases y with
      | row b =>
          have h : (⟨false, a⟩ : Σ i, Factor L R i) = ⟨false, b⟩ := hxy
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
          exact congrArg Syllable.row h
      | code b =>
          have h : (⟨false, a⟩ : Σ i, Factor L R i) = ⟨true, b⟩ := hxy
          simp at h
  | code a =>
      cases y with
      | row b =>
          have h : (⟨true, a⟩ : Σ i, Factor L R i) = ⟨false, b⟩ := hxy
          simp at h
      | code b =>
          have h : (⟨true, a⟩ : Σ i, Factor L R i) = ⟨true, b⟩ := hxy
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
          exact congrArg Syllable.code h

/-- The sigma reading of a syllable list determines the list. -/
theorem map_syllableToSigma_injective {L R : Type u} [Group L] [Group R] :
    Function.Injective
      (List.map (Syllable.toSigma : Syllable L R → Σ i, Factor L R i)) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => rfl
      | cons b u => simp at h
  | cons a t ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons b u =>
          rw [List.map_cons, List.map_cons, List.cons.injEq] at h
          rw [syllableToSigma_injective h.1, ih h.2]

theorem normalize_selected_eq_factors
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)}
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹) :
    normalize (selectedSyllableList m v.toWord) =
      normalize [.row left, .code (selectedAHom m B v), .row right⁻¹] := by
  classical
  let rhs : List (Syllable (FreeGroup (LowIndex m)) F₃) :=
    [.row left, .code (selectedAHom m B v), .row right⁻¹]
  have hrhs : evalList rhs =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹ := by
    simp [rhs, evalList, eval, mul_assoc]
  have hprod : (selectedNormalizedWord m v).prod =
      (normalizedWord rhs).prod := by
    rw [selectedNormalizedWord_prod, normalizedWord_prod, hrhs, hEq]
  have hword : selectedNormalizedWord m v = normalizedWord rhs := by
    apply CoprodI.Word.equiv.symm.injective
    exact hprod
  have hlists := congrArg CoprodI.Word.toList hword
  change (normalize (selectedSyllableList m v.toWord)).map Syllable.toSigma =
    (normalize rhs).map Syllable.toSigma at hlists
  simpa only [rhs] using map_syllableToSigma_injective hlists

theorem selectedStartsWithRow_iff_leftFactor_ne_one
    {m : ℕ} {B : Set E} {p : SelectedBlock m B × Bool}
    {L : List (SelectedBlock m B × Bool)} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)} (hv : v.toWord = p :: L)
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹) :
    selectedStartsWithRow p ↔ left ≠ 1 := by
  have hred : FreeGroup.IsReduced (p :: L) := by
    rw [← hv]
    exact FreeGroup.isReduced_toWord
  have hhead := normalize_selectedSyllableList_head p L hred
  have hnorm := normalize_selected_eq_factors hEq
  rw [hv] at hnorm
  have hcode : selectedAHom m B v ≠ 1 :=
    selectedAHom_ne_one_of_toWord_ne_nil (by rw [hv]; simp)
  constructor
  · intro hp hleft
    rcases hhead with ⟨_, q, hq⟩ | ⟨hnp, -, -⟩
    · rw [hq] at hnorm
      have hfirst := congrArg List.head? hnorm
      by_cases hright : right = 1 <;>
        simp [BinarySyllableNormalizer.normalize, prepend, hleft, hright,
          hcode] at hfirst
    · exact absurd hp hnp
  · intro hleft
    rcases hhead with ⟨hp, -, -⟩ | ⟨_, q, hq⟩
    · exact hp
    · rw [hq] at hnorm
      have hfirst := congrArg List.head? hnorm
      by_cases hright : right = 1 <;>
        simp [BinarySyllableNormalizer.normalize, prepend, hleft, hright,
          hcode] at hfirst

theorem lowRowFactor_eq_leftFactor_of_selectedStartsWithRow
    {m : ℕ} {B : Set E} {p : SelectedBlock m B × Bool}
    {L : List (SelectedBlock m B × Bool)} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)} (hv : v.toWord = p :: L)
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹)
    (hp : selectedStartsWithRow p) :
    lowRowFactor m (Seq.elt (p.1 : Seq.E)) = left := by
  have hred : FreeGroup.IsReduced (p :: L) := by
    rw [← hv]
    exact FreeGroup.isReduced_toWord
  have hhead := normalize_selectedSyllableList_head p L hred
  rcases hhead with ⟨_, q, hq⟩ | ⟨hnp, -, -⟩
  · have hnorm := normalize_selected_eq_factors hEq
    rw [hv, hq] at hnorm
    have hcode : selectedAHom m B v ≠ 1 :=
      selectedAHom_ne_one_of_toWord_ne_nil (by rw [hv]; simp)
    have hleft : left ≠ 1 :=
      (selectedStartsWithRow_iff_leftFactor_ne_one hv hEq).mp hp
    have hfirst := congrArg List.head? hnorm
    by_cases hright : right = 1 <;>
      simp [BinarySyllableNormalizer.normalize, prepend, hleft, hright,
        hcode] at hfirst
    all_goals exact hfirst
  · exact absurd hp hnp

theorem selectedIndexed_equation_inv_factors
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)}
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹) :
    selectedIndexedLinkHom m B v⁻¹ =
      CoprodI.of (i := false) right *
        CoprodI.of (i := true) (selectedAHom m B v⁻¹) *
          (CoprodI.of (i := false) left)⁻¹ := by
  rw [map_inv (selectedIndexedLinkHom m B) v, hEq,
    map_inv (selectedAHom m B) v]
  simp [mul_assoc]

theorem selectedEndsWithRow_iff_rightFactor_ne_one
    {m : ℕ} {B : Set E} {P : List (SelectedBlock m B × Bool)}
    {p : SelectedBlock m B × Bool} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)} (hv : v.toWord = P ++ [p])
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹) :
    selectedEndsWithRow p ↔ right ≠ 1 := by
  have hinvWord : v⁻¹.toWord =
      (p.1, !p.2) :: FreeGroup.invRev P := by
    rw [toWord_inv_eq_invRev, hv, FreeGroup.invRev_append]
    rfl
  have hhead := selectedStartsWithRow_iff_leftFactor_ne_one hinvWord
    (selectedIndexed_equation_inv_factors hEq)
  simpa [selectedEndsWithRow, selectedStartsWithRow] using hhead

theorem lowRowFactor_eq_rightFactor_of_selectedEndsWithRow
    {m : ℕ} {B : Set E} {P : List (SelectedBlock m B × Bool)}
    {p : SelectedBlock m B × Bool} {v : FreeGroup (SelectedBlock m B)}
    {left right : FreeGroup (LowIndex m)} (hv : v.toWord = P ++ [p])
    (hEq : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) left *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) right)⁻¹)
    (hp : selectedEndsWithRow p) :
    lowRowFactor m (Seq.elt (p.1 : Seq.E)) = right := by
  have hinvWord : v⁻¹.toWord =
      (p.1, !p.2) :: FreeGroup.invRev P := by
    rw [toWord_inv_eq_invRev, hv, FreeGroup.invRev_append]
    rfl
  obtain ⟨hsign, hne⟩ := hp
  have hstart : selectedStartsWithRow ((p.1, !p.2) : SelectedBlock m B × Bool) := by
    simp [selectedStartsWithRow, hsign, hne]
  have hres := lowRowFactor_eq_leftFactor_of_selectedStartsWithRow hinvWord
    (selectedIndexed_equation_inv_factors hEq) hstart
  exact hres

end Omega
end Higman
end GroupApproximation
