import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Computability.MFRecognitionPi02

/-!
# Axiom audit for the finite-presentation MF recognition hierarchy

The checker equivalence is parameterized by a presentation code, so it uses
the ordinary axiom audit.  The two hierarchy statements are closed
propositions and use the stronger closed-endpoint gate, which rejects both
unexpected axioms and hidden leading construction inputs.
-/

#audit_axioms GroupApproximation.MFRecognitionPi02.isOperatorMF_iff_forall_exists_MFChecker
#audit_closed_axioms GroupApproximation.MFRecognitionPi02.operatorMFCode_pi02
#audit_closed_axioms GroupApproximation.MFRecognitionPi02.nonOperatorMFCode_sigma02
