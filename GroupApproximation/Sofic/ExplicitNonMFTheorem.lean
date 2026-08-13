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
      MarkedCompressionGroup.theGroup where
  iota := MarkedCompressionGroup.theIota
  t := MarkedCompressionGroup.theT
  c := MarkedCompressionGroup.theC
  a := ExplicitNonMFBase.omitted
  kazhdan := ExplicitNonMFBase.base_hasKazhdanPropertyT
  compresses γ := ⟨ExplicitNonMFBase.compression γ,
    MarkedCompressionGroup.theCompress γ⟩
  comm_c := MarkedCompressionGroup.theCommC
  word_sq := MarkedCompressionGroup.theWordSq
  word_central := MarkedCompressionGroup.theWordCentral

/-- The countable Clifford witness group is itself not weak/operator-norm
MF: the finite presentation is needed only for finite presentability. -/
theorem countableWitness_not_isWeakMF :
    ¬ IsWeakMF MarkedCompressionGroup.theGroup :=
  witnessInclusionData.not_isWeakMF MarkedCompressionGroup.theWordNeOne

/-- Existence form: there is a countable group that is not
weak/operator-norm MF. -/
theorem exists_countable_not_isWeakMF :
    ∃ (E : Type) (_ : Group E), Countable E ∧ ¬ IsWeakMF E :=
  ⟨MarkedCompressionGroup.theGroup, inferInstance, inferInstance,
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
