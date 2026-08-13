import GroupApproximation.Sofic.ExplicitNonMFTheorem

/-!
# Lightweight axiom audit for the explicit non-MF endpoint

This deliberately imports only the public explicit theorem module.  It gives
reviewers and CI a fast audit target without replaying the much larger
project-wide endpoint audit.
-/

#print axioms GroupApproximation.ExplicitNonMFTheorem.mark_normMFInvisible
#print axioms GroupApproximation.ExplicitNonMFTheorem.explicit_finitelyPresented_not_isWeakMF
