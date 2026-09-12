import GroupApproximation.Higman.OmegaTowerSelectedLengthInduction

/-!
# The at-most-two nonzero selected-letter spelling

The binary syllable bound first reduces the canonical selected spelling to an
ordinary list containing at most two nonzero letters.  This file exposes that
finite list decomposition before the factor-endpoint comparison fixes the two
signs and the positions of any intervening zero letters.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

def selectedNonzeroLetters {m : ℕ} {B : Set E}
    (L : List (SelectedBlock m B × Bool)) :
    List (SelectedBlock m B × Bool) :=
  L.filter fun p => (p.1 : E) ≠ 0

def AllSelectedZero {m : ℕ} {B : Set E}
    (L : List (SelectedBlock m B × Bool)) : Prop :=
  ∀ p ∈ L, (p.1 : E) = 0

theorem selectedNonzeroLetters_eq_nil_iff_allZero
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)} :
    selectedNonzeroLetters L = [] ↔ AllSelectedZero L := by
  rw [selectedNonzeroLetters, List.filter_eq_nil_iff]
  simp [AllSelectedZero]

theorem decompose_of_selectedNonzeroLetters_eq_singleton
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    {p : SelectedBlock m B × Bool}
    (h : selectedNonzeroLetters L = [p]) :
    ∃ Z₁ Z₂, L = Z₁ ++ p :: Z₂ ∧ AllSelectedZero Z₁ ∧ AllSelectedZero Z₂ := by
  induction L with
  | nil => simp [selectedNonzeroLetters] at h
  | cons q L ih =>
      by_cases hq : (q.1 : E) = 0
      · have ht : selectedNonzeroLetters L = [p] := by
          simpa [selectedNonzeroLetters, hq] using h
        obtain ⟨Z₁, Z₂, hL, hZ₁, hZ₂⟩ := ih ht
        exact ⟨q :: Z₁, Z₂, by simp [hL],
          by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hq
            · exact hZ₁ z hz,
          hZ₂⟩
      · have hpq : q = p := by
          simpa [selectedNonzeroLetters, hq] using congrArg List.head? h
        subst q
        have ht : selectedNonzeroLetters L = [] := by
          simpa [selectedNonzeroLetters, hq] using h
        exact ⟨[], L, by simp, by simp [AllSelectedZero],
          selectedNonzeroLetters_eq_nil_iff_allZero.mp ht⟩

theorem decompose_of_selectedNonzeroLetters_eq_pair
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    {p q : SelectedBlock m B × Bool}
    (h : selectedNonzeroLetters L = [p, q]) :
    ∃ Z₀ Z₁ Z₂, L = Z₀ ++ p :: (Z₁ ++ q :: Z₂) ∧
      AllSelectedZero Z₀ ∧ AllSelectedZero Z₁ ∧ AllSelectedZero Z₂ := by
  induction L with
  | nil => simp [selectedNonzeroLetters] at h
  | cons r L ih =>
      by_cases hr : (r.1 : E) = 0
      · have ht : selectedNonzeroLetters L = [p, q] := by
          simpa [selectedNonzeroLetters, hr] using h
        obtain ⟨Z₀, Z₁, Z₂, hL, hZ₀, hZ₁, hZ₂⟩ := ih ht
        exact ⟨r :: Z₀, Z₁, Z₂, by simp [hL],
          by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hr
            · exact hZ₀ z hz,
          hZ₁, hZ₂⟩
      · have hrp : r = p := by
          simpa [selectedNonzeroLetters, hr] using congrArg List.head? h
        subst r
        have ht : selectedNonzeroLetters L = [q] := by
          simpa [selectedNonzeroLetters, hr] using h
        obtain ⟨Z₁, Z₂, hL, hZ₁, hZ₂⟩ :=
          decompose_of_selectedNonzeroLetters_eq_singleton ht
        exact ⟨[], Z₁, Z₂, by simp [hL], by simp [AllSelectedZero], hZ₁, hZ₂⟩

theorem selectedNonzeroCount_eq_length_nonzeroLetters
    {m : ℕ} {B : Set E} (L : List (SelectedBlock m B × Bool)) :
    selectedNonzeroCount L = (selectedNonzeroLetters L).length := rfl

theorem selectedNonzeroLetters_cases_of_count_le_two
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    (hcount : selectedNonzeroCount L ≤ 2) :
    selectedNonzeroLetters L = [] ∨
      (∃ p, selectedNonzeroLetters L = [p]) ∨
      (∃ p q, selectedNonzeroLetters L = [p, q]) := by
  rw [selectedNonzeroCount_eq_length_nonzeroLetters] at hcount
  generalize hW : selectedNonzeroLetters L = W at hcount ⊢
  cases W with
  | nil => exact Or.inl rfl
  | cons p W =>
      cases W with
      | nil => exact Or.inr (Or.inl ⟨p, rfl⟩)
      | cons q W =>
          cases W with
          | nil => exact Or.inr (Or.inr ⟨p, q, rfl⟩)
          | cons r W => simp at hcount

theorem selectedNonzeroLetters_cases_of_indexed_equation
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)} {l f : E}
    (hEq : selectedIndexedLinkHom m B v =
      Monoid.CoprodI.of (i := false) (lowRowFactor m (elt l)) *
        Monoid.CoprodI.of (i := true) (selectedAHom m B v) *
          (Monoid.CoprodI.of (i := false) (lowRowFactor m (elt f)))⁻¹) :
    selectedNonzeroLetters v.toWord = [] ∨
      (∃ p, selectedNonzeroLetters v.toWord = [p]) ∨
      (∃ p q, selectedNonzeroLetters v.toWord = [p, q]) :=
  selectedNonzeroLetters_cases_of_count_le_two
    (selectedNonzeroCount_toWord_le_two_of_indexed_equation hEq)

end Omega
end Higman
end GroupApproximation
