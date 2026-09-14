import GroupApproximation.Manuscript.NonMFSentences.CoreModelsLEF
import GroupApproximation.Dynamics.SubshiftCycleLEF
import GroupApproximation.Dynamics.CoreSubshiftCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# `R_Y` is LEF, closed

`non_mf_groups_exist.tex`, Lemma `lem:chain-core-models` (tex line 1372): "The set $Y$ is nonempty,
closed and invariant, and $R_Y$ is LEF."

`coreModelsLEFStatement_of_inputs` (`CoreModelsLEF`) proves `DynamicRankBudget.CoreModelsLEFStatement` along the
printed general-X route over two symbolic inputs, and the subshift case proves both:

* `WordGraph.isLEFRing_clopenCrossedProduct_of_cycleCondition` (tex 1386–1400: "A subshift satisfying the cycle
  condition has an LEF crossed product");
* `ChainCore.cycleCondition_coreSubshift` (tex 1410–1412: "Consequently $Y_0$ satisfies the cycle condition too").

## Manuscript status

Closed endpoint for the clause "$R_Y$ is LEF" of `lem:chain-core-models`.
-/

namespace GroupApproximation
namespace ChainCore

/-- The cycle-condition LEF theorem, as the input of the general-X route. -/
theorem subshiftCycleConditionLEFInput : SubshiftCycleConditionLEFInput := by
  intro A _ _ _ Z hZc hZ TZ hTZ hcyc k _ _
  exact WordGraph.isLEFRing_clopenCrossedProduct_of_cycleCondition hZc hZ TZ hTZ hcyc k

/-- The cycle condition of the symbolic core, as the input of the general-X route. -/
theorem subshiftCoreCycleConditionInput : SubshiftCoreCycleConditionInput := by
  intro A _ _ _ Z hZc hZ
  exact cycleCondition_coreSubshift hZc hZ

/-- **`R_Y` is LEF** (`lem:chain-core-models`, tex 1372). -/
theorem coreModelsLEFStatement : DynamicRankBudget.CoreModelsLEFStatement :=
  coreModelsLEFStatement_of_inputs subshiftCycleConditionLEFInput subshiftCoreCycleConditionInput

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.subshiftCycleConditionLEFInput
#audit_axioms GroupApproximation.ChainCore.subshiftCoreCycleConditionInput
#audit_closed_axioms GroupApproximation.ChainCore.coreModelsLEFStatement
