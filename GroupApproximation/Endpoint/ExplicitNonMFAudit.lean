import GroupApproximation.Sofic.ExplicitNonMFTheorem
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction

/-!
# Lightweight axiom audit for the explicit non-MF endpoint

This deliberately imports the public explicit theorem module together with
the finite-normal criterion whose endpoints are printed below.  It gives
reviewers and CI a fast audit target without replaying the much larger
project-wide endpoint audit.  The reported closure contains only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; no mathematical or
literature theorem is accepted as an axiom or premise of the closed non-MF
endpoint.
-/

#print axioms GroupApproximation.ExplicitNonMFTheorem.mark_normMFInvisible
#print axioms GroupApproximation.ExplicitNonMFTheorem.explicit_finitelyPresented_not_isWeakMF
#print axioms GroupApproximation.ExplicitNonMFTheorem.explicit_finitelyPresented_not_isOperatorMF
#print axioms GroupApproximation.ExplicitNonMFTheorem.countableWitness_not_isOperatorMF
#print axioms GroupApproximation.ExplicitNonMFTheorem.exists_finitelyPresented_not_isOperatorMF
#print axioms GroupApproximation.ExplicitNonMFTheorem.not_every_group_isOperatorMF
#print axioms GroupApproximation.ExplicitNonMFTheorem.not_every_finitelyPresented_group_isOperatorMF
#print axioms GroupApproximation.KazhdanCompressionCore.finiteNormal_le_normMFResidual
#print axioms GroupApproximation.KazhdanCompressionCore.not_isOperatorMF_of_finiteNormal_le_defect
#print axioms GroupApproximation.isOperatorMF_iff_normMFResidual_eq_bot
#print axioms GroupApproximation.KazhdanCompressionCore.finiteNormal_le_normMatrixCoronaKernel
#print axioms GroupApproximation.coronaMFResidual_eq_normMFResidual
#print axioms GroupApproximation.map_coronaMFResidual_le
#print axioms GroupApproximation.isOperatorMF_iff_coronaMFResidual_eq_bot
