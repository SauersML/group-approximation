import GroupApproximation.Manuscript.OneSidedMFRadical.CornerClassIdentificationKazhdan
import GroupApproximation.Meta.AxiomGuard

/-!
# Axiom audit of the corner-class identification

Both headline endpoints are named `Prop`s with every binder inside the
statement, so `#audit_closed_axioms` applies to them directly.
-/

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCornerCoronaClassIdentification

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoordinateGramRepresentsPrintedB

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.exists_coordinateNormBound_of_correctedCornerKazhdan

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.correctedCornerSectorGramSequence_class
