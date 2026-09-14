import GroupApproximation.Dynamics.ItineraryCoreCycleCondition
import GroupApproximation.Dynamics.CoreSubshiftCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:chain-core-models`: the intersection keeps the cycle condition, closed

`non_mf_groups_exist.tex`, proof of Lemma `lem:chain-core-models` (tex 1439–1441):

> The sets on its right decrease and satisfy the cycle condition; finite language stabilization proves
> that their intersection does too.

`cycleCondition_itinerary_image_generalCore` carries the sentence along the printed route, over the named
hypothesis `hcore : ∀ l, CycleCondition (itineraryCore T (S l))`.  That hypothesis is tex 1411, "Consequently
$Y_0$ satisfies the cycle condition too", for the itinerary subshifts, and it is closed:
`cycleCondition_coreSubshift` holds for every closed shift-invariant subshift over a finite alphabet.  This
module states the sentence as a named Prop and proves it with nothing assumed.

* `PrintedItineraryIntersectionCycleCondition`, `printedItineraryIntersectionCycleCondition`: for every compact
  `X`, homeomorphism `T` and antitone sequence of finite clopen partitions `S`, every itinerary image
  `π_m(Y_*) = ⋂_{l≥m} ρ_lm(Y_l)` satisfies the cycle condition.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

/-- **"finite language stabilization proves that their intersection does too"** (tex 1439–1441): the
itinerary image `π_m(Y_*)` of the inverse-limit core satisfies the cycle condition. -/
def PrintedItineraryIntersectionCycleCondition : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X) (S : ℕ → DiscreteQuotient X),
    Antitone S → ∀ m : ℕ, CycleCondition (itinerary T (S m) '' generalCore T S)

theorem printedItineraryIntersectionCycleCondition : PrintedItineraryIntersectionCycleCondition := by
  intro X _ _ T S hS m
  exact cycleCondition_itinerary_image_generalCore T hS
    (fun l ↦ cycleCondition_coreSubshift (isClosed_itinerarySubshift T (S l))
      (mapsTo_shift_itinerarySubshift T (S l))) m

end ChainCore
end GroupApproximation

#audit_closed_axioms GroupApproximation.ChainCore.printedItineraryIntersectionCycleCondition
