import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

/-!
# MF input for the tensor-synchronized coordinates
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint

open Filter PolarLiftingGeneralCStar
open TensorSynchronizationAssembly
open HNNCoronaConjugatorSentenceAudit

noncomputable section

universe u v

noncomputable local instance tensorMFCoordinatePartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorMFCoordinateStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The bundled C-star structure on the tensor-coordinate corona, named so
specialized endpoints can pass it without repeating deep typeclass search. -/
@[reducible] noncomputable def tensorCoordinateCoronaCStarAlgebra
    {A : Type v} [CStarAlgebra A] [Nontrivial A]
    (G B : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (B n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (B n)]
    [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (B n)] :
    CStarAlgebra (CStarProductCorona
      (fun n ↦ TensorCoordinateAlgebra A (fun n ↦ G n × B n) n) cofinite) :=
  inferInstance

/-- Each tensor coordinate in the manuscript construction has an MF
embedding. -/
theorem manuscriptTensorCoordinate_hasMF
    {Gamma : Type v} [Group Gamma]
    {A : Type v} [CStarAlgebra A] [Nontrivial A]
    (G B : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (B n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (B n)]
    [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (B n)]
    (R : RegularRealizationData Gamma A) (n : ℕ) :
    HasMFEmbedding
      (TensorCoordinateAlgebra A (fun n ↦ G n × B n) n) :=
  (synchronizedCoordinate_isMF (fun n ↦ G n × B n) R n).2

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint
