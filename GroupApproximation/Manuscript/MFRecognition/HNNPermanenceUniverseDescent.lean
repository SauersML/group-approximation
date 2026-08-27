import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalArvesonExtension
import GroupApproximation.Analysis.NonUnitalMFSupportCornerEmbedding
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCoordinateCore

/-!
# Removing the universe artefact from HNN permanence

The universal C-star HNN algebra lives in `Type 1`, while
`IsRegularlyRealized` asks for a realization algebra in `Type`.  This file
removes that formalization artefact without an assumption.  A faithful unital
corona representation identifies the large algebra with its closed represented
range.  That range is a C-star subalgebra of a `Type`-valued matrix corona, so
it is itself small.  The group representation and trace transport across the
resulting star-algebra equivalence.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
open GroupApproximation.BlackadarKirchberg

noncomputable section

/-- A regular realization in a possibly large C-star algebra can be replaced
by one in the closed represented range of a faithful unital matrix-corona
embedding.  The represented range is a small type, so this proves the exact
universe-descent statement used by HNN permanence. -/
theorem regularRealizationDescent_proved
    {R : Type} [Group R] [Countable R] {B : Type 1} [CStarAlgebra B]
    (hB : RegularRealizationData R B) : IsRegularlyRealized R := by
  letI : Nontrivial B := regularRealization_nontrivial hB
  obtain ⟨Y, hY, _hYpos, _hYmono, e₀, he₀⟩ := hB.mf.2
  letI : ∀ n, Nonempty (Y n) := hY
  obtain ⟨X, hX, e, he⟩ :=
    NonUnitalMFSupportCornerEmbedding.exists_injective_unital_supportCornerEmbedding
      Y e₀ he₀
  letI : ∀ n, Nonempty (X n) := hX
  let C : StarSubalgebra ℂ (NormMatrixCStarCorona (fun n ↦ X n)) :=
    starAlgHomRange e
  have hCclosed : IsClosed (C : Set (NormMatrixCStarCorona (fun n ↦ X n))) :=
    isClosed_starAlgHomRange e
  letI : CStarAlgebra C :=
    { toNormedRing := inferInstance
      toStarRing := inferInstance
      toCompleteSpace := hCclosed.completeSpace_coe
      toCStarRing := inferInstance
      toNormedAlgebra := C.toSubalgebra.toNormedAlgebra
      toStarModule := StarSubalgebra.starModule C }
  let er : B ≃⋆ₐ[ℂ] C := starAlgEquivRange e he
  have hCmf : IsMFAlgebra C :=
    hB.mf.of_injective_nonUnitalStarAlgHom
      er.symm.toStarAlgHom.toNonUnitalStarAlgHom er.symm.injective
  let rhoC : R →* unitary C :=
    (unitaryMapOfStarAlgHom er.toStarAlgHom).comp hB.rho
  let tauC : TracialState C := hB.tau.compStarAlgHom er.symm.toStarAlgHom
  refine ⟨C, inferInstance, ⟨
    { mf := hCmf
      rho := rhoC
      tau := tauC
      regular := ?_ }⟩⟩
  intro g hg
  change hB.tau (er.symm (er ((hB.rho g : unitary B) : B))) = 0
  rw [er.symm_apply_apply]
  exact hB.regular g hg

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
