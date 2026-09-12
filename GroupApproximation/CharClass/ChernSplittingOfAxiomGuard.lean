import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.CharClass.ChernSplittingOfFlag

/-!
# Gating axiom audit for the splitting principle over `K`

Lane `lix-evenside`.  Every declaration of `ChernSplittingOfPowers`, `ChernSplittingOfInjective`,
`ChernSplittingOfWhitney` and `ChernSplittingOfFlag`, checked with `#audit_axioms`, which throws
unless the closure is exactly `[propext, Classical.choice, Quot.sound]`.  A `Built` line for this
module is the certificate.  Every declaration is conditional, so `#audit_closed_axioms` is not
used.
-/

namespace GroupApproximation.CharClass

/-! ### `ChernSplittingOfPowers.lean` -/

#audit_axioms evenCoe
#audit_axioms evenCoe_apply
#audit_axioms evenCoe_injective
#audit_axioms SplittingDataOf
#audit_axioms SplittingDataOf.evenRoot
#audit_axioms SplittingDataOf.powerData
#audit_axioms hasSplittingP_of_splittingDataOf
#audit_axioms ParityP.HasSplittingP.elim

/-! ### `ChernSplittingOfInjective.lean` -/

#audit_axioms ChernSplittingOf.totalHOf_map_id
#audit_axioms ChernSplittingOf.totalHOf_map_comp
#audit_axioms ChernSplittingOf.totalHOf_component_map
#audit_axioms ChernSplittingOf.totalHOf_map_injective
#audit_axioms ChernSplittingOf.totalHOf_map_injective_comp
#audit_axioms ChernSplittingOf.totalHOf_map_injective_of_leftInv
#audit_axioms ChernSplittingOf.flagForget_map_injective
#audit_axioms ChernSplittingOf.flagProj_zero_map_injective
#audit_axioms ChernSplittingOf.flagProj_map_injective
#audit_axioms ChernSplittingOf.flagProj_map_injective_of_proj

/-! ### `ChernSplittingOfWhitney.lean` -/

#audit_axioms ChernSplittingOf.chern_eq_coeff
#audit_axioms ChernSplittingOf.chern_split_of_splitPoly
#audit_axioms ChernSplittingOf.splittingDataOf_of_splitPoly
#audit_axioms ChernSplittingOf.aeval_taut_map
#audit_axioms ChernSplittingOf.splitPoly_of_splitRelation
#audit_axioms ChernSplittingOf.hasSplittingP_of_splitRelation

/-! ### `ChernSplittingOfFlag.lean` -/

#audit_axioms ChernSplittingOf.flag_square
#audit_axioms ChernSplittingOf.hasSplittingP_flag

end GroupApproximation.CharClass
