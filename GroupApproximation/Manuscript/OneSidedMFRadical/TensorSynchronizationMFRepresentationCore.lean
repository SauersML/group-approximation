import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

/-!
# The tensor-synchronized representation used by the manuscript endpoint

Naming the representation keeps the endpoint theorem's type from repeatedly
normalizing the full synchronized-adjoining construction.
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint

open Filter PolarLiftingGeneralCStar
open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationAssembly

noncomputable section

universe u v w

noncomputable local instance tensorMFRepresentationPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorMFRepresentationStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The corona-valued representation produced from the manuscript's finite
quotient data. -/
def manuscriptSynchronizedRepresentation
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A] [Nontrivial A]
    (G B : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (B n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (B n)]
    [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (B n)]
    (R : RegularRealizationData Gamma A)
    (iota : S →* Gamma) (tau : S →* Q)
    (lambda : ∀ n, Gamma →* G n) (beta : ∀ n, Q →* B n)
    (hker : ∀ n, ((lambda n).comp iota).ker ≤ ((beta n).comp tau).ker) :
    Monoid.Coprod (Gamma × Q) (Multiplicative ℤ) →
      unitary (CStarProductCorona
        (fun n ↦ TensorCoordinateAlgebra A (fun n ↦ G n × B n) n) cofinite) :=
  fun x ↦ synchronizedAdjoinedHom
    (fun n ↦ G n × B n) R
    (fun n ↦ productFiniteQuotientHom (lambda n) (beta n))
    (tensorSynchronizationSource (Q := Q) iota)
    (tensorSynchronizationTarget iota tau)
    (fun _ ↦ rfl)
    (fun n ↦ productFiniteQuotient_source_target_ker_eq
      iota tau (lambda n) (beta n) (hker n)) x

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint
