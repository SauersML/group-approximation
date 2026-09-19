import GroupApproximation.Sofic.LiteralNonMFPresentation
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Exact finite-radius bound for the literal presentation

The companion note advertises radius `34` for the explicit marked-group
cylinder.  This file checks the combinatorial part of that claim directly
against the Lean definitions: the marked word has reduced length at most
`16`, and every one of the finitely generated displayed relators has reduced
length at most `34`.
-/

namespace GroupApproximation
namespace LiteralPresentationRadius

open LiteralNonMFPresentation

noncomputable section

/-- Canonical reduced-word length, stated for the literal generator type. -/
def wordLength (w : FreeGroup Generator) : ℕ := w.toWord.length

/-- The displayed marked commutator has reduced length at most sixteen. -/
theorem markedWord_length_le : wordLength markedWord ≤ 16 := by
  decide

private theorem transportedBaseRelator_length_le
    {r : FreeGroup Generator} (hr : r ∈ transportedBaseRelators) :
    wordLength r ≤ 12 := by
  classical
  rw [transportedBaseRelators] at hr
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  rw [mem_baseRelators_iff] at hq
  rcases hq with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem stableRelator_length_le
    {r : FreeGroup Generator} (hr : r ∈ stableRelators) :
    wordLength r ≤ 12 := by
  classical
  rw [stableRelators] at hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
  fin_cases i <;> decide

private theorem lampRelator_length_le
    {r : FreeGroup Generator} (hr : r ∈ lampRelators) :
    wordLength r ≤ 6 := by
  classical
  rw [lampRelators, Finset.mem_union] at hr
  rcases hr with hr | hr
  · simp only [Finset.mem_singleton] at hr
    subst r
    decide
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    fin_cases i <;> decide

private theorem markedRelator_length_le
    {r : FreeGroup Generator} (hr : r ∈ markedRelators) :
    wordLength r ≤ 34 := by
  classical
  rw [markedRelators] at hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
  rcases i with i | i <;> fin_cases i <;> decide

/-- Every relator in the literal eight-generator presentation lies in the
canonical reduced-word ball of radius `34`. -/
theorem relator_wordLength_le_34
    {r : FreeGroup Generator} (hr : r ∈ relators) :
    wordLength r ≤ 34 := by
  classical
  change r ∈
    ((transportedBaseRelators ∪ stableRelators) ∪ lampRelators) ∪
      markedRelators at hr
  simp only [Finset.mem_union] at hr
  rcases hr with ((htransported | hstable) | hlamp) | hmarked
  · exact (transportedBaseRelator_length_le htransported).trans (by norm_num)
  · exact (stableRelator_length_le hstable).trans (by norm_num)
  · exact (lampRelator_length_le hlamp).trans (by norm_num)
  · exact markedRelator_length_le hmarked

/-- The finite Horn control set—every relator together with the marked
word—is contained in reduced radius `34`. -/
theorem relators_or_markedWord_length_le_34
    {q : FreeGroup Generator} (hq : q ∈ relators ∨ q = markedWord) :
    wordLength q ≤ 34 := by
  rcases hq with hrel | rfl
  · exact relator_wordLength_le_34 hrel
  · exact markedWord_length_le.trans (by norm_num)

end
end LiteralPresentationRadius
end GroupApproximation
