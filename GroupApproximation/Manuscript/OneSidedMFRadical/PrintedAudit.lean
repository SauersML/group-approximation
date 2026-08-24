import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed-endpoint audit: the printed defect and the compression criterion

`#audit_closed_axioms` fails the build both when the axiom closure of a proof
reaches beyond `propext`, `Classical.choice`, `Quot.sound` and when the
declaration's type begins with a caller-supplied binder.  Every statement
below is therefore machine-checked to be unconditional: the manuscript's
quantifiers live inside the named propositions, and nothing is accepted as
mathematical input from a caller.
-/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFiniteDimensionalSterility
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets
