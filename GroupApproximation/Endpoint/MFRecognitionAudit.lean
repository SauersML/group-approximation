import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Computability.MFRecognitionImpossible

/-!
# Axiom audit for `NONMF ∉ RE` and the undecidability of MF recognition

Every line below is `#audit_closed_axioms`, which fails the build on two
distinct defects: an axiom outside `propext`, `Classical.choice`, `Quot.sound`
anywhere in the transitive closure, and a leading declaration input in the
statement.  The second is the one that matters for these endpoints.  An
undecidability corollary is the natural place to smuggle in an Adian--Rabin
theorem as a premise, and a report that reads "no disallowed axioms" would look
identical whether the theorem were proved or accepted.  Refusing a leading
binder makes the difference machine-visible: these statements accept no
transformation, no reduction datum, and no computability fact from a caller.

`isFinitelyPresented_carrier` is audited with `#audit_axioms` instead, because
its subject is the code it quantifies over; it is a fact about the coding
rather than an advertised endpoint.
-/

#audit_axioms GroupApproximation.MFRecognitionImpossible.isFinitelyPresented_carrier
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.exists_mf_presentation
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.exists_nonMF_presentation
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.exists_manyOne_reduction_wordProblem_to_operatorMF
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.exists_halting_reduction_to_operatorMF
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.mf_recognition_not_computable
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.no_mf_decider
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.nonMF_presentations_not_re
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.no_nonMF_enumerator
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.no_total_nonMF_enumerator
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.mf_recognition_impossible
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.torsionFreeMF_recognition_not_computable
#audit_closed_axioms GroupApproximation.MFRecognitionImpossible.torsionFreeMF_negative_side_not_re
#audit_closed_axioms GroupApproximation.Computability.operatorMF_recognition_not_computable
#audit_closed_axioms GroupApproximation.WordProblemRE.operatorMF_negative_side_not_re
#audit_closed_axioms GroupApproximation.Computability.not_computablePred_wordProblemPred
#audit_closed_axioms GroupApproximation.WordProblemRE.not_rePred_compl_wordProblemPred
#audit_axioms GroupApproximation.WordProblemRE.rePred_wordProblemPred
