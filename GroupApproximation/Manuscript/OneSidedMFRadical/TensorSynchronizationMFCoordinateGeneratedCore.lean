import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFGeneratedCore
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFCoordinateCore

/-!
# MF permanence for generated subalgebras of the tensor-coordinate corona
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint

open Filter PolarLiftingGeneralCStar
open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationAssembly

noncomputable section

universe u v w

noncomputable local instance tensorMFCoordinateGeneratedPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorMFCoordinateGeneratedStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- A countably generated subalgebra of the tensor-coordinate corona is MF. -/
theorem tensorCoordinateGeneratedCStar_isMF
    {Gamma : Type v} [Group Gamma]
    {A : Type v} [CStarAlgebra A] [Nontrivial A]
    (G B : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (B n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (B n)]
    [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (B n)]
    (R : RegularRealizationData Gamma A)
    {H : Type w} [Countable H]
    (rho : H → unitary (CStarProductCorona
      (fun n ↦ TensorCoordinateAlgebra A (fun n ↦ G n × B n) n) cofinite)) :
    IsMFAlgebra (SynchronizedGeneratedCStar rho) :=
  synchronizedGeneratedCStar_isMF
    (fun n ↦ TensorCoordinateAlgebra A (fun n ↦ G n × B n) n)
    rho (manuscriptTensorCoordinate_hasMF G B R)

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint
