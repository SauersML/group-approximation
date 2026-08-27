import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFCoordinateGeneratedCore
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFRepresentationCore

/-!
# Manuscript specialization of tensor-synchronized MF permanence
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint

open Filter PolarLiftingGeneralCStar
open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationAssembly

noncomputable section

universe u v w

noncomputable local instance tensorMFManuscriptPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorMFManuscriptStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The MF conclusion in the exact input language of the manuscript. -/
theorem manuscriptSynchronizedGeneratedCStar_isMF
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma] [Countable Gamma]
    {Q : Type u} [Group Q] [Countable Q]
    {A : Type v} [CStarAlgebra A] [Nontrivial A]
    (G B : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (B n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (B n)]
    [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (B n)]
    (R : RegularRealizationData Gamma A)
    (iota : S →* Gamma) (tau : S →* Q)
    (lambda : ∀ n, Gamma →* G n) (beta : ∀ n, Q →* B n)
    (hker : ∀ n, ((lambda n).comp iota).ker ≤ ((beta n).comp tau).ker) :
    let rho := manuscriptSynchronizedRepresentation
      G B R iota tau lambda beta hker
    let D := CStarProductCorona
      (fun n ↦ TensorCoordinateAlgebra A (fun n ↦ G n × B n) n) cofinite
    let ambient := tensorCoordinateCoronaCStarAlgebra G B
    let C := @SynchronizedGeneratedCStar
      (Monoid.Coprod (Gamma × Q) (Multiplicative ℤ)) D ambient rho
    @IsMFAlgebra C
      (@synchronizedGeneratedCStar_cStarAlgebra
        (Monoid.Coprod (Gamma × Q) (Multiplicative ℤ)) D ambient rho).toNonUnitalCStarAlgebra := by
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.ofAdd
  letI : Countable (Monoid.Coprod (Gamma × Q) (Multiplicative ℤ)) :=
    Monoid.Coprod.mk_surjective.countable
  exact tensorCoordinateGeneratedCStar_isMF G B R
    (manuscriptSynchronizedRepresentation G B R iota tau lambda beta hker)

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint
