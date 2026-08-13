import GroupApproximation.Sofic.ExplicitNonMFEndpoint
import GroupApproximation.Sofic.MarkedCompressionSequentialKill

/-!
# The explicit finitely presented non-MF group

This module is the public junction between the independently checkable
finite-presentation construction in `ExplicitNonMFEndpoint` and the analytic
marked-compression kill theorem.  It exports both forms of the main result:

* the concrete nontrivial mark belongs to the universal operator-norm MF
  residual, so every homomorphism to every norm matrix ultraproduct kills it;
* the concrete finitely presented group is therefore not weak/MF.
-/

namespace GroupApproximation
namespace ExplicitNonMFTheorem

open ExplicitMarkedPresentation ExplicitNonMFEndpoint

/-- The universal marked-compression certificate carried by the explicit
finite presentation. -/
noncomputable def normCertificate :
    MarkedCompressionNormCertificate MarkedGroup :=
  inclusionData.normCertificate inclusionData_word_ne_one

/-- The concrete nontrivial central mark is killed by every homomorphism to
every operator-norm matrix ultraproduct. -/
theorem mark_normMFInvisible : NormMFInvisible mark := by
  rw [← inclusionData_word]
  exact inclusionData.word_normMFInvisible

/-- The explicit finitely presented marked-compression group is not
weak/operator-norm MF. -/
theorem explicit_finitelyPresented_not_isWeakMF :
    Group.IsFinitelyPresented MarkedGroup ∧ ¬ IsWeakMF MarkedGroup :=
  ⟨inferInstance, normCertificate.not_isWeakMF⟩

end ExplicitNonMFTheorem
end GroupApproximation
