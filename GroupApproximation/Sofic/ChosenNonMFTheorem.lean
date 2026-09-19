import GroupApproximation.Sofic.ChosenNonMFEndpoint
import GroupApproximation.Sofic.MarkedCompressionExplicitGroup
import GroupApproximation.Sofic.MarkedCompressionSequentialKill

/-!
# A finitely presented non-MF group from the Shalom-cover construction

This module is the public junction between the independently checkable
finite-presentation construction in `ChosenNonMFEndpoint` and the analytic
marked-compression kill theorem.  The formal witness uses a noncomputably
chosen finitely presented Kazhdan cover.  The existence theorem for that
cover, the property-`(T)` theorem for the compressor base, and every analytic
input consumed below are proved in this repository: no literature theorem is
introduced as a premise or axiom.  Noncomputability here is only
`Classical.choice` selecting data from the proved existence theorem.

The chosen cover is not definitionally the displayed finite presentation used
in the paper.  This module exports both forms of the main result:

* the chosen witness's nontrivial mark belongs to the universal operator-norm MF
  residual, so every homomorphism to every norm matrix ultraproduct kills it;
* that finitely presented group is therefore neither weak-MF nor MF
  in the standard cofinite norm-matrix-corona sense.
-/

namespace GroupApproximation
namespace ChosenNonMFTheorem

open ChosenMarkedPresentation ChosenNonMFEndpoint

/-- The universal marked-compression certificate carried by the
Shalom-cover finite presentation chosen in `ChosenMarkedPresentation`. -/
noncomputable def normCertificate :
    MarkedCompressionNormCertificate MarkedGroup :=
  inclusionData.normCertificate inclusionData_word_ne_one

/-- The chosen presentation's nontrivial central mark is killed by every
homomorphism to every operator-norm matrix ultraproduct. -/
theorem mark_normMFInvisible : NormMFInvisible mark := by
  rw [← inclusionData_word]
  exact inclusionData.word_normMFInvisible

/-- The finitely presented Shalom-cover marked-compression group is not
weak/operator-norm MF. -/
theorem chosenFinitelyPresented_not_isWeakMF :
    Group.IsFinitelyPresented MarkedGroup ∧ ¬ IsWeakMF MarkedGroup :=
  ⟨inferInstance, normCertificate.not_isWeakMF⟩

/-- **Unconditional operator-MF counterexample.**  The finitely presented
Shalom-cover marked-compression group is not MF in the standard cofinite
norm-matrix-corona sense.  This theorem has no mathematical premise; all
load-bearing construction and rigidity theorems are proved in-repository.
("Unconditional" refers to the absence of premises, not to any topological
closedness.) -/
theorem chosenFinitelyPresented_not_isOperatorMF :
    Group.IsFinitelyPresented MarkedGroup ∧ ¬ IsOperatorMF MarkedGroup :=
  ⟨inferInstance, inclusionData.not_isOperatorMF inclusionData_word_ne_one⟩

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

/-- The countable Clifford witness is not MF in the standard cofinite
norm-matrix-corona sense. -/
theorem countableWitness_not_isOperatorMF :
    ¬ IsOperatorMF MarkedCompression.Explicit.theGroup :=
  witnessInclusionData.not_isOperatorMF MarkedCompression.Explicit.theWordNeOne

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
    chosenFinitelyPresented_not_isWeakMF.1,
    chosenFinitelyPresented_not_isWeakMF.2⟩

/-- There exists a finitely presented group that is not MF in the standard
cofinite norm-matrix-corona sense. -/
theorem exists_finitelyPresented_not_isOperatorMF :
    ∃ (E : Type) (_ : Group E),
      Group.IsFinitelyPresented E ∧ ¬ IsOperatorMF E :=
  ⟨MarkedGroup, inferInstance,
    chosenFinitelyPresented_not_isOperatorMF.1,
    chosenFinitelyPresented_not_isOperatorMF.2⟩

/-- A single witness carrying both countability and finite presentability. -/
theorem exists_countable_finitelyPresented_not_isOperatorMF :
    ∃ (E : Type) (_ : Group E),
      Countable E ∧ Group.IsFinitelyPresented E ∧ ¬ IsOperatorMF E :=
  ⟨MarkedGroup, inferInstance, inferInstance,
    chosenFinitelyPresented_not_isOperatorMF.1,
    chosenFinitelyPresented_not_isOperatorMF.2⟩

/-- The universal operator-MF assertion fails even after restricting to
countable groups. -/
theorem not_every_countable_group_isOperatorMF :
    ¬ (∀ (E : Type) [Group E] [Countable E], IsOperatorMF E) := by
  intro hall
  exact chosenFinitelyPresented_not_isOperatorMF.2 (hall MarkedGroup)

/-- **Negative solution of the universal operator-MF problem.**  Not every
group embeds in a cofinite norm-matrix corona. -/
theorem not_every_group_isOperatorMF :
    ¬ (∀ (E : Type) [Group E], IsOperatorMF E) := by
  intro hall
  obtain ⟨E, groupE, _hfp, hE⟩ :=
    exists_finitelyPresented_not_isOperatorMF
  letI : Group E := groupE
  exact hE (hall E)

/-- The universal operator-MF assertion already fails inside the class of
finitely presented groups. -/
theorem not_every_finitelyPresented_group_isOperatorMF :
    ¬ (∀ (E : Type) [Group E] [Group.IsFinitelyPresented E],
      IsOperatorMF E) := by
  intro hall
  obtain ⟨E, groupE, hfp, hE⟩ :=
    exists_finitelyPresented_not_isOperatorMF
  letI : Group E := groupE
  letI : Group.IsFinitelyPresented E := hfp
  exact hE (hall E)

end ChosenNonMFTheorem
end GroupApproximation
