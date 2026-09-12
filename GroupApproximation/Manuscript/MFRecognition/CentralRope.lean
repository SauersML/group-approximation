import GroupApproximation.Manuscript.MFRecognition.CentralRopeBritton
import GroupApproximation.Meta.AxiomGuard

/-!
# `mf_recognition_complexity.tex`, `lem:central-rope`

This public module assembles the first central-rope construction and its
Britton normal-form proof.  The implementation is split between
`CentralRopeCore` and `CentralRopeBritton`; importing this module exposes the
same theorem names as the manuscript.
-/

open GroupApproximation
open GroupApproximation.Manuscript.MFRecognition.Rope.RopeInput

#audit_axioms amalgamToGamma_injective
#audit_axioms amalgamHom_injective
#audit_axioms amalgamHom_surjective
#audit_axioms amalgamEquiv
