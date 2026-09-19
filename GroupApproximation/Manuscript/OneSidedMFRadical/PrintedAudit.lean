import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem
import GroupApproximation.Manuscript.OneSidedMFRadical.CanonicalSector
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
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanPrintedRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanCoronaVanishing
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCriterionAssembly
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectCoronaVanishing

-- **Theorem B.**  `EL₁₂(L_{𝔽₂}(1,2))` is simple, has full MF radical, and is
-- not MF.  Both the support theorem and the exact full headline have empty
-- caller telescopes.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittFullRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionSimple
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittHeadline
