import GroupApproximation.Sofic.MFRelationClosure
import GroupApproximation.Sofic.RadicalFunctoriality

/-!
# MF residual calculus for the one-sided Kazhdan manuscript

This module is the manuscript-facing statement for
`non_mf_groups_exist.tex`, Proposition `prop:mf-residual-calculus`.

The proposition is deliberately packaged as a closed `Prop`. The group and
normal-subgroup quantifiers live inside the proposition, so the endpoint can
be checked by `#audit_closed_axioms` without accepting mathematical input from
its caller.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u

/-- Quotients of countable groups are countable. -/
local instance quotientCountable {G : Type*} [Group G]
    (N : Subgroup G) [hN : N.Normal] [Countable G] : Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- **Proposition `prop:mf-residual-calculus`.** The literal genuine-corona
MF radical is fully invariant, its universal quotient is MF, MF quotients are
exactly the fixed points of semantic MF closure, and a countable group is MF
exactly when its radical is trivial. -/
def MFResidualCalculus : Prop :=
  ∀ (G : Type u) [Group G] [Countable G],
    RadicalFunctoriality.IsFullyInvariant (actualCoronaMFResidual G) ∧
      IsCDEOperatorMF (G ⧸ actualCoronaMFResidual G) ∧
      (∀ (N : Subgroup G) [N.Normal],
        (IsCDEOperatorMF (G ⧸ N) ↔ actualCoronaMFClosure N = N)) ∧
      (IsCDEOperatorMF G ↔ actualCoronaMFResidual G = ⊥)

/-- Closed proof of the manuscript's MF residual-calculus proposition. -/
theorem manuscriptMFResidualCalculus : MFResidualCalculus := by
  intro G _ _
  refine ⟨?_, actualCoronaMFQuotient_isCDEOperatorMF, ?_,
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot⟩
  · intro f
    exact map_actualCoronaMFResidual_le f
  · intro N _
    exact (actualCoronaMFClosure_eq_self_iff N).symm

end OneSidedMFRadical
end Manuscript
end GroupApproximation
