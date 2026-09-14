import GroupApproximation.Manuscript.NonMFSentences.CoreModelsLEFClosed
import GroupApproximation.Dynamics.CoreSubshiftCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# The first sentence of the chain-recurrent core lemma

`non_mf_groups_exist.tex`, Lemma `lem:chain-core-models` (tex line 1372):

> The set $Y$ is nonempty, closed and invariant, and $R_Y$ is LEF.

* `chainRecurrentSet_nonempty`: `Y = CR(T)` is nonempty.  Every itinerary subshift is nonempty, so every
  itinerary core is (`coreSubshift_nonempty`, tex 1408–1409).  The inverse-limit core `Y_*` is then nonempty
  (`inverseLimitCore_nonempty`), and `Y_* = Y` (`generalCore_eq_chainRecurrentSet`, tex 1454).
* `printedChainCoreModelsFirstSentence`: the whole sentence, with the closed and invariant clauses from
  `Dynamics.isClosed_chainRecurrentSet` and `Dynamics.image_chainRecurrentSet`, and the LEF clause from
  `coreModelsLEFStatement`.

## Manuscript status

Closed endpoint for the first sentence of `lem:chain-core-models` (tex 1372).
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph GroupApproximation.Dynamics

section Nonempty

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] (T : X ≃ₜ X)

/-- Every itinerary core is nonempty. -/
theorem itineraryCore_nonempty (S' : DiscreteQuotient X) : (itineraryCore T S').Nonempty :=
  coreSubshift_nonempty (mapsTo_shift_itinerarySubshift T S') (range_nonempty (itinerary T S'))

/-- The inverse-limit core `Y_*` is nonempty. -/
theorem generalCore_nonempty {S : ℕ → DiscreteQuotient X} (hS : Antitone S) :
    (generalCore T S).Nonempty :=
  inverseLimitCore_nonempty T hS (fun m ↦ itineraryCore_subset T (S m))
    (fun h ↦ oneBlock_image_itineraryCore_subset (T := T) (hS h))
    (fun m ↦ isClosed_itineraryCore T (S m)) (fun m ↦ itineraryCore_nonempty T (S m))

end Nonempty

/-- **"The set $Y$ is nonempty"** (`lem:chain-core-models`, tex 1372). -/
theorem chainRecurrentSet_nonempty {X : Type*} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) : (chainRecurrentSet T).Nonempty := by
  obtain ⟨S, hS⟩ := exists_refiningClopenPartitions (X := X)
  rw [← generalCore_eq_chainRecurrentSet T hS]
  exact generalCore_nonempty T hS.antitone

/-- **`lem:chain-core-models`, first sentence** (tex 1372): "The set $Y$ is nonempty, closed and invariant,
and $R_Y$ is LEF", for a nonempty compact metrizable zero-dimensional `X`, a homeomorphism `T`, and a finite
field `k`. -/
def PrintedChainCoreModelsFirstSentence : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k],
    (chainRecurrentSet T).Nonempty ∧ IsClosed (chainRecurrentSet T) ∧
      T '' chainRecurrentSet T = chainRecurrentSet T ∧
      Pestov91.IsLEFRing
        (ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T (DynamicRankBudget.image_core T)) k)

theorem printedChainCoreModelsFirstSentence : PrintedChainCoreModelsFirstSentence := by
  intro X _ _ _ _ T k _ _
  exact ⟨chainRecurrentSet_nonempty T, isClosed_chainRecurrentSet T.continuous,
    image_chainRecurrentSet T, coreModelsLEFStatement X T k⟩

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.itineraryCore_nonempty
#audit_axioms GroupApproximation.ChainCore.generalCore_nonempty
#audit_axioms GroupApproximation.ChainCore.chainRecurrentSet_nonempty
#audit_closed_axioms GroupApproximation.ChainCore.printedChainCoreModelsFirstSentence
