import GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientBothInclusions
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:leavitt-mf-quotient`: `EL_d(R) ≤ [H,H]`, closed

`non_mf_groups_exist.tex`, the last sentence of the proof of Corollary `cor:leavitt-mf-quotient`
(census row `f6962254d259`):

> So `[H,H] ≤ EL_d(R)`, while `EL_d(R) ≤ [H,H]` because every homomorphism from `EL_d(R)`
> to an MF group is trivial (Theorem `thm:full-defect-ring`).

`elementary_le_commutator_of_trivial` proves the third clause from its printed reason, taken as an inline
premise: every homomorphism from `EL_d(R)` to an MF group is trivial.  That premise is Theorem
`thm:full-defect-ring` at `R = L_k(1,d)` and rank `d`, which is closed
(`FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics`).  This
module states the clause as a named Prop and proves it with nothing assumed.

* `PrintedElementaryLeCommutator`, `printedElementaryLeCommutator_closed`: for every countable field `k`
  and every `d ≥ 2`, `EL_d(L_k(1,d)) ≤ [GL_d(L_k(1,d)), GL_d(L_k(1,d))]`, along the printed route.
-/

namespace GroupApproximation
namespace LeavittMFQuotientBothInclusions

open AryLeavitt Manuscript.OneSidedMFRadical

/-- **"`EL_d(R) ≤ [H,H]` because every homomorphism from `EL_d(R)` to an MF group is trivial"**
(tex 1307), for every countable field `k` and every `d ≥ 2`, with `R = L_k(1,d)` and `H = GL_d(R)`. -/
def PrintedElementaryLeCommutator : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (d : ℕ), 2 ≤ d →
    elementaryGroup (Fin d) (AryLeavittAlgebra k d) ≤
      commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ

/-- **The third clause, closed.**  The printed reason is Theorem `thm:full-defect-ring` at `L_k(1,d)`
and rank `d`, and `elementary_le_commutator_of_trivial` turns it into the inclusion. -/
theorem printedElementaryLeCommutator_closed : PrintedElementaryLeCommutator := by
  intro k _ _ d hd
  exact elementary_le_commutator_of_trivial k d fun M _ hM ↦
    FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics
      k d hd d hd M hM

end LeavittMFQuotientBothInclusions
end GroupApproximation

#audit_closed_axioms
  GroupApproximation.LeavittMFQuotientBothInclusions.printedElementaryLeCommutator_closed
