import GroupApproximation.Sofic.ExplicitNonMFEndpoint
import GroupApproximation.Sofic.MarkedCompressionGroup
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

/-- The countable Clifford witness group bundled as marked-compression
inclusion data. -/
noncomputable def witnessInclusionData :
    MarkedCompressionInclusionData ExplicitNonMFBase.Base
      MarkedCompression.Explicit.theGroup where
  iota := MarkedCompression.Explicit.theIota
  t := MarkedCompression.Explicit.theT
  c := MarkedCompression.Explicit.theC
  a := ExplicitNonMFBase.omitted
  kazhdan := ExplicitNonMFBase.base_hasKazhdanPropertyT
  compresses γ := ⟨ExplicitNonMFBase.compression γ,
    MarkedCompression.Explicit.theCompress γ⟩
  comm_c := MarkedCompression.Explicit.theCommC
  word_sq := MarkedCompression.Explicit.theWordSq
  word_central := MarkedCompression.Explicit.theWordCentral

/-- The countable Clifford witness group is itself not weak/operator-norm
MF: the finite presentation is needed only for finite presentability. -/
theorem countableWitness_not_isWeakMF :
    ¬ IsWeakMF MarkedCompression.Explicit.theGroup :=
  witnessInclusionData.not_isWeakMF MarkedCompression.Explicit.theWordNeOne

/-- Existence form: there is a countable group that is not
weak/operator-norm MF. -/
theorem exists_countable_not_isWeakMF :
    ∃ (E : Type) (_ : Group E), Countable E ∧ ¬ IsWeakMF E :=
  ⟨MarkedCompression.Explicit.theGroup, inferInstance, inferInstance,
    countableWitness_not_isWeakMF⟩

/-- Existence form: there is a finitely presented group that is not
weak/operator-norm MF. -/
theorem exists_finitelyPresented_not_isWeakMF :
    ∃ (E : Type) (_ : Group E),
      Group.IsFinitelyPresented E ∧ ¬ IsWeakMF E :=
  ⟨MarkedGroup, inferInstance,
    explicit_finitelyPresented_not_isWeakMF.1,
    explicit_finitelyPresented_not_isWeakMF.2⟩

end ExplicitNonMFTheorem
end GroupApproximation
