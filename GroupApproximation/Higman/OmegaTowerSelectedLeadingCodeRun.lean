import GroupApproximation.Higman.OmegaTowerSelectedCodeRuns
import GroupApproximation.Higman.OmegaTowerSelectedNormalizedFactors

/-!
# The maximal initial code run of a selected spelling

The raw binary expansion begins in the code factor except at a negative
nonzero letter.  Zero letters contribute code only and extend that run; a
positive nonzero letter contributes its code and then terminates the run with
its row syllable.  This file reifies that precise initial segment and proves
its value is nontrivial in every nonempty reduced selected spelling.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq
open GroupApproximation.Higman.Conj

def selectedStartsWithRow {m : ℕ} {B : Set E}
    (p : SelectedBlock m B × Bool) : Prop :=
  p.2 = false ∧ (p.1 : E) ≠ 0

/-- The signed selected letters whose code contributions form the maximal
initial right-factor run of the raw expansion. -/
noncomputable def leadingSelectedCodeRun {m : ℕ} {B : Set E} :
    List (SelectedBlock m B × Bool) →
      List (SelectedBlock m B × Bool) := by
  classical
  exact fun
    | [] => []
    | p :: L =>
        if selectedStartsWithRow p then []
        else if (p.1 : E) = 0 then p :: leadingSelectedCodeRun L
        else [p]

theorem leadingSelectedCodeRun_prefix
    {m : ℕ} {B : Set E} :
    ∀ L : List (SelectedBlock m B × Bool),
      leadingSelectedCodeRun L <+: L := by
  intro L
  induction L with
  | nil => exact List.nil_prefix
  | cons p L ih =>
      by_cases hrow : selectedStartsWithRow p
      · rw [leadingSelectedCodeRun, if_pos hrow]
        exact List.nil_prefix
      · by_cases hzero : (p.1 : E) = 0
        · rw [leadingSelectedCodeRun, if_neg hrow, if_pos hzero]
          obtain ⟨q, hq⟩ := ih
          exact ⟨q, by simpa using congrArg (List.cons p) hq⟩
        · rw [leadingSelectedCodeRun, if_neg hrow, if_neg hzero]
          exact ⟨L, rfl⟩

theorem leadingSelectedCodeRun_ne_nil_of_not_startsWithRow
    {m : ℕ} {B : Set E} (p : SelectedBlock m B × Bool)
    (L : List (SelectedBlock m B × Bool))
    (hrow : ¬ selectedStartsWithRow p) :
    leadingSelectedCodeRun (p :: L) ≠ [] := by
  by_cases hzero : (p.1 : E) = 0 <;>
    simp [leadingSelectedCodeRun, hrow, hzero]

noncomputable def selectedCodeRunValue
    {m : ℕ} {B : Set E} (L : List (SelectedBlock m B × Bool)) : F₃ :=
  (L.map fun p => if p.2 then aElt (p.1 : E) else (aElt (p.1 : E))⁻¹).prod

theorem selectedCodeRunValue_eq_selectedAHom_mk
    {m : ℕ} {B : Set E} (L : List (SelectedBlock m B × Bool)) :
    selectedCodeRunValue L = selectedAHom m B (FreeGroup.mk L) := by
  induction L with
  | nil =>
      change 1 = selectedAHom m B 1
      rw [map_one]
  | cons p L ih =>
      have hmk : FreeGroup.mk (p :: L) =
          FreeGroup.mk [p] * FreeGroup.mk L := by
        rw [FreeGroup.mul_mk]
        rfl
      rcases p with ⟨beta, s⟩
      cases s with
      | false =>
          have hsingle : FreeGroup.mk [(beta, false)] =
              (FreeGroup.of beta)⁻¹ := by
            show FreeGroup.mk [(beta, false)] =
              (FreeGroup.mk [(beta, true)])⁻¹
            rw [FreeGroup.inv_mk]
            rfl
          change (aElt (beta : E))⁻¹ * selectedCodeRunValue L = _
          rw [hmk, map_mul, hsingle, map_inv, selectedAHom_of, ih]
      | true =>
          have hsingle : FreeGroup.mk [(beta, true)] = FreeGroup.of beta := rfl
          change aElt (beta : E) * selectedCodeRunValue L = _
          rw [hmk, map_mul, hsingle, selectedAHom_of, ih]

/-- A nonempty initial code run never disappears.  This includes a run made
entirely of signed zero-block letters. -/
theorem leadingSelectedCodeRun_value_ne_one
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    (hred : FreeGroup.IsReduced L)
    (hne : leadingSelectedCodeRun L ≠ []) :
    selectedCodeRunValue (leadingSelectedCodeRun L) ≠ 1 := by
  rw [selectedCodeRunValue_eq_selectedAHom_mk]
  apply selectedAHom_mk_ne_one_of_isReduced _ hne
  have hpref := leadingSelectedCodeRun_prefix L
  obtain ⟨q, hq⟩ := hpref
  rw [← hq] at hred
  exact (List.isChain_append.mp hred).1

/-- The code contribution of one letter followed by the maximal initial code
run of its tail is nontrivial.  This is the exact product tested when a code
syllable is prepended to an already normalized tail. -/
theorem cons_leadingSelectedCodeRun_value_ne_one
    {m : ℕ} {B : Set E} {p : SelectedBlock m B × Bool}
    {L : List (SelectedBlock m B × Bool)}
    (hred : FreeGroup.IsReduced (p :: L)) :
    selectedCodeRunValue (p :: leadingSelectedCodeRun L) ≠ 1 := by
  rw [selectedCodeRunValue_eq_selectedAHom_mk]
  apply selectedAHom_mk_ne_one_of_isReduced _ (List.cons_ne_nil _ _)
  have hpref := leadingSelectedCodeRun_prefix L
  obtain ⟨q, hq⟩ := hpref
  have hprefix : p :: leadingSelectedCodeRun L <+: p :: L := by
    exact ⟨q, by simpa using congrArg (List.cons p) hq⟩
  obtain ⟨r, hr⟩ := hprefix
  rw [← hr] at hred
  exact (List.isChain_append.mp hred).1

end Omega
end Higman
end GroupApproximation
