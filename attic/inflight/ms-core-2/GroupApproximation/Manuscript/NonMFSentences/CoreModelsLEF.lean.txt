import GroupApproximation.Dynamics.ChainCoreGeneralLEF
import GroupApproximation.Dynamics.ChainCoreGeneralRecurrent
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Meta.AxiomGuard

/-!
# `R_Y` is LEF

`non_mf_groups_exist.tex`, Lemma `lem:chain-core-models` (tex line 1372): "The set $Y$ is nonempty,
closed and invariant, and $R_Y$ is LEF."  This module carries the clause "$R_Y$ is LEF" in ct-rank-budget's
spelling `DynamicRankBudget.CoreModelsLEFStatement`, along the printed general-X route (tex 1428–1454):

* choose refining clopen partitions (`exists_refiningClopenPartitions`);
* `R_{Y_*}` is LEF (`isLEFRing_clopenCrossedProduct_generalCore`);
* `Y_* = Y` (`generalCore_eq_chainRecurrentSet`).

The two symbolic inputs of the subshift case (tex 1386 and 1411) are explicit hypotheses here:
`SubshiftCycleConditionLEFInput` (the cycle condition makes the crossed product LEF) and
`SubshiftCoreCycleConditionInput` (the symbolic core satisfies the cycle condition).  Both belong to the
symbolic lane.

## Manuscript status

Intermediate: `coreModelsLEFStatement_of_inputs` proves `CoreModelsLEFStatement` over the two symbolic
inputs; the closed endpoint follows once they land.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

/-- **Input: the symbolic core satisfies the cycle condition** (tex 1411: "Consequently $Y_0$ satisfies
the cycle condition too"). -/
def SubshiftCoreCycleConditionInput : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (Z : Set (ℤ → A)),
    IsClosed Z → (∀ n : ℤ, MapsTo (shift n) Z Z) → CycleCondition (coreSubshift Z)

section Transport

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k]

/-- The crossed product of an invariant set depends only on the set. -/
theorem isLEFRing_restrictHomeo_of_eq {Y Y' : Set X} (hY : T '' Y = Y) (hY' : T '' Y' = Y')
    (h : Y = Y')
    (hLEF : Pestov91.IsLEFRing (ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T hY) k)) :
    Pestov91.IsLEFRing (ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T hY') k) := by
  subst h
  exact hLEF

end Transport

/-- **`R_Y` is LEF** (`lem:chain-core-models`, tex 1372), along the printed general-X route, over the two
symbolic inputs of the subshift case. -/
theorem coreModelsLEFStatement_of_inputs (hLEF : SubshiftCycleConditionLEFInput)
    (hcyc : SubshiftCoreCycleConditionInput) : DynamicRankBudget.CoreModelsLEFStatement := by
  intro X _ _ _ _ T k _ _
  obtain ⟨S, hS⟩ := exists_refiningClopenPartitions (X := X)
  have hcore : ∀ l, CycleCondition (itineraryCore T (S l)) := fun l ↦
    hcyc (S l) (itinerarySubshift T (S l)) (isClosed_itinerarySubshift T (S l))
      (mapsTo_shift_itinerarySubshift T (S l))
  exact isLEFRing_restrictHomeo_of_eq T k (image_generalCore T S) (DynamicRankBudget.image_core T)
    (generalCore_eq_chainRecurrentSet T hS)
    (isLEFRing_clopenCrossedProduct_generalCore T hS hLEF hcore k)

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.isLEFRing_restrictHomeo_of_eq
#audit_axioms GroupApproximation.ChainCore.coreModelsLEFStatement_of_inputs
