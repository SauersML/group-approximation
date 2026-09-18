import GroupApproximation.Analysis.MatrixModelFormPositivity
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros into matrix-sequence coronas: from cp maps to form-positive maps

Lane `nm-tww-08`, step 5. The coordinates are completely positive in the
`CStarExactness.IsCompletelyPositive` sense, as maps into the C-star algebra `M_Y`.
The interface asks for the form sense `Quasidiagonal.IsCompletelyPositiveOnMatrices`.
This file supplies that bridge.

Proof route.
* `euclideanize Y : M_Y → B(ℓ²(Fin |Y|))` is the underlying linear map of a
  `⋆`-homomorphism, namely reindexing followed by `Matrix.toEuclideanCLM`. So it is
  completely positive (`isCompletelyPositive_of_starAlgHom`).
* For a cp `ψ : A → M_Y`, the composite `euclideanize Y ∘ ψ` is cp. The corpus lemma
  `isCompletelyPositiveOnMatrices_matrixOfEuclidean` makes
  `a ↦ matrixOfEuclidean Y (euclideanize Y (ψ a))` form-positive.
* `matrixOfEuclidean_euclideanize` says this map is `ψ`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CoronaChoiEffros

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForCoronaChoiEffrosForm
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.matrixBlockCStarAlgebraForCoronaChoiEffrosForm

/-- `Quasidiagonal.euclideanize` as a non-unital `⋆`-homomorphism. -/
def euclideanizeStarHom (Y : FiniteModel) :
    Matrix Y Y ℂ →⋆ₙₐ[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) :=
  ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (Fintype.card Y))).toStarAlgHom.comp
    (matrixReindexStarAlgEquiv (Quasidiagonal.enum Y)).toStarAlgHom).toNonUnitalStarAlgHom

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.euclideanizeStarHom

/-- Reindexing to `ℓ²` is completely positive. -/
theorem isCompletelyPositive_euclideanize (Y : FiniteModel) [Nonempty Y] :
    IsCompletelyPositive (Quasidiagonal.euclideanize Y) := by
  have hEq : Quasidiagonal.euclideanize Y =
      (euclideanizeStarHom Y : Matrix Y Y ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Fintype.card Y)))) :=
    LinearMap.ext fun _ ↦ rfl
  rw [hEq]
  exact isCompletelyPositive_of_starAlgHom (euclideanizeStarHom Y)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.isCompletelyPositive_euclideanize

/-- **cp implies form-positive.** A completely positive linear map `A → M_Y` is
completely positive in the matrix-form sense of `Quasidiagonal`. -/
theorem isCompletelyPositiveOnMatrices_of_isCompletelyPositive {A : Type u}
    [CStarAlgebra A] (Y : FiniteModel) [Nonempty Y] (ψ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (hψ : IsCompletelyPositive ψ) :
    Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑ψ := by
  have hform := LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean Y
    (Quasidiagonal.euclideanize Y ∘ₗ ψ) ((isCompletelyPositive_euclideanize Y).comp hψ)
  have hfun : (fun a : A ↦
      LocalLifting.matrixOfEuclidean Y ((Quasidiagonal.euclideanize Y ∘ₗ ψ) a)) = ⇑ψ := by
    funext a
    exact LocalLifting.matrixOfEuclidean_euclideanize Y (ψ a)
  rw [← hfun]
  exact hform

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.isCompletelyPositiveOnMatrices_of_isCompletelyPositive

end

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
