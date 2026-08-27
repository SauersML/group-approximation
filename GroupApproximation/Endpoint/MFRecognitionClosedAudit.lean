import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.MFRecognition.RecognitionDebts
import GroupApproximation.Manuscript.NonMF.TheoremCDebts

/-!
# Axiom audit for `thm:recognition` and Theorem C, closed

`Assembly.manuscriptRecognition` is a closed proposition: every printed clause
of `thm:recognition` (the `Π⁰₂`/`Σ⁰₂` upper bounds, both completeness
clauses, undecidability, the two non-r.e. clauses and the reduction from
`INF`).  `TheoremC.manuscriptTorsionFreeFullMFRadical_closed` and
`manuscriptTorsionFreeSimplified_closed` are the closed forms of Theorem C of
the non-MF paper.

Each is subjected to the closed-endpoint gate, which rejects unexpected axioms
(in particular `sorryAx`) and hidden leading construction inputs.  This module
enters the root import list only once every recorded debt in
`RecognitionDebts` and `TheoremCDebts` is discharged; until then it is
deliberately not imported, since the gate would fail on the debts it exists
to certify against.
-/

#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HigmanCompiler.Assembly.manuscriptRecognition
#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HigmanCompiler.Assembly.mfPresentations_pi02Complete
#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HigmanCompiler.Assembly.nonMFPresentations_sigma02Complete
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_closed
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_closed
#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HigmanCompiler.Assembly.reBenign
