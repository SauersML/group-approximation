import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGeneratedRestrictionCore

/-!
# Covariance in the tensor-synchronized generated algebra
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open PolarLiftingGeneralCStar Filter

noncomputable section

universe u v w

noncomputable local instance tensorGeneratedCovariancePartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorGeneratedCovarianceStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- Covariance holds inside the synchronized generated algebra itself. -/
theorem synchronizedGeneratedConjugator_covariance
    {S : Type w} [Group S] {G : Type v} [Group G]
    {D : Type u} [CStarAlgebra D]
    (rho : Monoid.Coprod G (Multiplicative ℤ) →* unitary D)
    (source target : S →* G)
    (hcov : ∀ s : S,
      (rho (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) : D) *
          (rho (Monoid.Coprod.inl (source s)) : D) *
        star (rho (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) : D) =
      (rho (Monoid.Coprod.inl (target s)) : D))
    (s : S) :
    let V := synchronizedGeneratedProductHom rho
    let W := synchronizedGeneratedConjugator rho
    (W : SynchronizedGeneratedCStar (fun x ↦ rho x)) *
          (V (source s) : SynchronizedGeneratedCStar (fun x ↦ rho x)) *
        star (W : SynchronizedGeneratedCStar (fun x ↦ rho x)) =
      (V (target s) : SynchronizedGeneratedCStar (fun x ↦ rho x)) := by
  apply Subtype.ext
  change
    (((synchronizedGeneratedConjugator rho :
        unitary (SynchronizedGeneratedCStar (fun x ↦ rho x))) :
      SynchronizedGeneratedCStar (fun x ↦ rho x)) : D) *
        (((synchronizedGeneratedProductHom rho (source s) :
            unitary (SynchronizedGeneratedCStar (fun x ↦ rho x))) :
          SynchronizedGeneratedCStar (fun x ↦ rho x)) : D) *
      star (((synchronizedGeneratedConjugator rho :
          unitary (SynchronizedGeneratedCStar (fun x ↦ rho x))) :
        SynchronizedGeneratedCStar (fun x ↦ rho x)) : D) =
    (((synchronizedGeneratedProductHom rho (target s) :
        unitary (SynchronizedGeneratedCStar (fun x ↦ rho x))) :
      SynchronizedGeneratedCStar (fun x ↦ rho x)) : D)
  rw [coe_synchronizedGeneratedConjugator,
    coe_synchronizedGeneratedProductHom,
    coe_synchronizedGeneratedProductHom]
  exact hcov s

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
