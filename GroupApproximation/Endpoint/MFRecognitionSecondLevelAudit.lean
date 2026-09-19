import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Computability.MFRecognitionSecondLevel

/-!
# Axiom audit for the exact second-level MF recognition shell

The completeness package intentionally exposes its one construction input,
`MFCompiler`.  The no-decider theorem is closed and is therefore subjected to
the stronger closed-endpoint audit.
-/

#audit_axioms GroupApproximation.MFRecognitionSecondLevel.mfCode_pi02Complete_of_compiler
#audit_axioms GroupApproximation.MFRecognitionSecondLevel.nonMFCode_sigma02Complete_of_compiler
#audit_axioms GroupApproximation.MFRecognitionSecondLevel.finitePresentationMF_secondLevel_package
#audit_closed_axioms GroupApproximation.MFRecognitionSecondLevel.no_finitePresentation_MF_decider
