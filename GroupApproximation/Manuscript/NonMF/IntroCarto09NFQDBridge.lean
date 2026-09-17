import GroupApproximation.Manuscript.NonMF.IntroCarto09NFQDReduction
import GroupApproximation.Analysis.LanceNFUnitalCPAP
import GroupApproximation.Analysis.MatrixModelFormPositivity
import GroupApproximation.Meta.AxiomGuard

/-!
# NF ⇒ quasidiagonal: the CP bridge

Lane `nm-intro-09`. This proves
`IntroCarto09.CompletelyPositiveOnMatricesBridgeStatement`: a map
`φ : A → M_Y` that is completely positive in the factorization sense
`CStarExactness.IsCompletelyPositive` is completely positive in the entrywise
form sense `Quasidiagonal.IsCompletelyPositiveOnMatrices`.

## Proof route

* `CStarExactness.finiteModelOperatorStarAlgEquiv Y : M_Y ≃⋆ₐ B(ℓ²(Fin |Y|))` is
  a ⋆-isomorphism, so its linear map is completely positive
  (`isCompletelyPositive_of_starAlgHom`). The composite `Ψ = e ∘ φ` is
  therefore completely positive (`IsCompletelyPositive.comp`).
* `LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean` shows that
  `matrixOfEuclidean Y ∘ Ψ` is form-positive.
* `matrixOfEuclidean Y (e M) = M`, because `e` is definitionally
  `Quasidiagonal.euclideanize Y` and `matrixOfEuclidean_euclideanize` applies.
  Hence `matrixOfEuclidean Y ∘ Ψ = φ`, and the form-positivity transfers.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto09

open CStarExactness
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-- Matrix blocks at the scoped operator norm are C⋆-algebras (the instance of
`Analysis/NFAlgebra.lean`, field for field). -/
local instance matrixBlockCStarAlgebraForIntroCarto09Bridge (Z : Type)
    [Fintype Z] [DecidableEq Z] [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **Factorization-sense complete positivity gives form-sense complete
positivity** for maps into a positive-dimensional matrix block. -/
theorem isCompletelyPositiveOnMatrices_of_isCompletelyPositive {A : Type u}
    [CStarAlgebra A] (Y : FiniteModel) [Nonempty Y]
    (φ : A →ₗ[ℂ] Matrix Y Y ℂ) (hφ : IsCompletelyPositive φ) :
    Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑φ := by
  have heCP : IsCompletelyPositive
      (BlackadarKirchberg.starAlgEquivLinearMap
        (finiteModelOperatorStarAlgEquiv Y)) :=
    isCompletelyPositive_of_starAlgHom
      (finiteModelOperatorStarAlgEquiv Y).toStarAlgHom.toNonUnitalStarAlgHom
  have hΨ : IsCompletelyPositive
      (BlackadarKirchberg.starAlgEquivLinearMap
        (finiteModelOperatorStarAlgEquiv Y) ∘ₗ φ) :=
    heCP.comp hφ
  have hback : ∀ x : A,
      LocalLifting.matrixOfEuclidean Y
        ((BlackadarKirchberg.starAlgEquivLinearMap
          (finiteModelOperatorStarAlgEquiv Y) ∘ₗ φ) x) = φ x := by
    intro x
    rw [LinearMap.comp_apply, BlackadarKirchberg.starAlgEquivLinearMap_apply]
    exact LocalLifting.matrixOfEuclidean_euclideanize Y (φ x)
  have hfun : (fun a : A ↦ LocalLifting.matrixOfEuclidean Y
      ((BlackadarKirchberg.starAlgEquivLinearMap
        (finiteModelOperatorStarAlgEquiv Y) ∘ₗ φ) a)) = ⇑φ :=
    funext hback
  have h := LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean Y
    (BlackadarKirchberg.starAlgEquivLinearMap
      (finiteModelOperatorStarAlgEquiv Y) ∘ₗ φ) hΨ
  rw [← hfun]
  exact h

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.isCompletelyPositiveOnMatrices_of_isCompletelyPositive

/-- **The CP bridge**, closed. -/
theorem completelyPositiveOnMatricesBridge :
    CompletelyPositiveOnMatricesBridgeStatement.{u} :=
  fun _ _ Y _ φ hφ ↦ isCompletelyPositiveOnMatrices_of_isCompletelyPositive Y φ hφ

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.completelyPositiveOnMatricesBridge

end

end IntroCarto09
end NonMF
end Manuscript
end GroupApproximation
