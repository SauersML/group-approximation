import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsHolds
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar decomposition and Kasparov stabilization: unconditional form

Lane `nm-tww-17a` (`Polar/AbsHolds.lean`) proves `AbsOperatorStatement B`. Lane `nm-tww-17b`
(`Polar/ExtendEndpoint.lean`) reduces the polar unitary and Kasparov stabilization to it.
Plugging one into the other gives the unconditional endpoints below.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Lance, Prop. 3.8**: the polar unitary exists. -/
theorem polarUnitaryStatement_holds : PolarUnitaryStatement B :=
  polarUnitary_of_absOperator absOperatorStatement_holds

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.polarUnitaryStatement_holds

/-- **Kasparov stabilization**, unconditionally. -/
theorem kasparovStabilizationStatement_holds : KasparovStabilizationStatement B :=
  kasparovStabilization_of_absOperator absOperatorStatement_holds

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.kasparovStabilizationStatement_holds

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
