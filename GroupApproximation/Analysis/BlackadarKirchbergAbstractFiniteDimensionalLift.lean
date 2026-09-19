import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalLift
import GroupApproximation.Analysis.BlackadarKirchbergStarEquivTransport
import GroupApproximation.Analysis.FiniteDimensionalCStarMatrixCPRetract
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Meta.AxiomGuard

/-!
# CPC lifts from abstract finite-dimensional C-star algebras

The concrete Choi--Effros lift in
`BlackadarKirchbergFiniteDimensionalLift` has a full matrix domain.  Every
nontrivial finite-dimensional C-star algebra is a UCP retract of one full
matrix algebra, so composing with that retract before lifting and with its
embedding afterwards gives the abstract finite-dimensional version.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u w

variable {X : ℕ → Type u} [∀ n, Fintype (X n)]
  [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]

local instance boundedMatrixSequenceCStarAlgebraForAbstractFiniteLift :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance matrixBlockCStarAlgebraForAbstractFiniteLift
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Every CPC map from a nontrivial finite-dimensional C-star algebra into a
norm-matrix corona has an exact CPC lift to the bounded matrix product. -/
theorem exists_completelyPositiveContractive_finiteDimensional_lift
    {D : Type w} [CStarAlgebra D] [Nontrivial D] [FiniteDimensional ℂ D]
    (f : D →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : IsCompletelyPositive f)
    (hfContractive : ∀ d, ‖f d‖ ≤ ‖d‖) :
    ∃ lift : D →ₗ[ℂ] BoundedMatrixSequence X,
      IsCompletelyPositive lift ∧
        (∀ d, ‖lift d‖ ≤ ‖d‖) ∧
        ∀ d, normMatrixCStarCoronaQuotient X (lift d) = f d := by
  obtain ⟨R⟩ := exists_matrixUCPRetract_of_finiteDimensionalCStar D
  let fMatrix : Matrix R.model R.model ℂ →ₗ[ℂ]
      NormMatrixCStarCorona X := f.comp R.retract
  have hfMatrixCP : IsCompletelyPositive fMatrix :=
    hf.comp R.retract_completelyPositive
  have hfMatrixContractive : ∀ T, ‖fMatrix T‖ ≤ ‖T‖ := by
    intro T
    exact (hfContractive (R.retract T)).trans (R.retract_norm_le T)
  let reindex : Matrix R.model R.model ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (Fintype.card R.model)) (Fin (Fintype.card R.model)) ℂ :=
    matrixReindexStarAlgEquiv (Fintype.equivFin R.model)
  let fFin : Matrix (Fin (Fintype.card R.model))
      (Fin (Fintype.card R.model)) ℂ →ₗ[ℂ] NormMatrixCStarCorona X :=
    fMatrix.comp (starAlgEquivLinearMap reindex.symm)
  have hfFinCP : IsCompletelyPositive fFin :=
    isCompletelyPositive_comp_starAlgEquiv reindex.symm fMatrix hfMatrixCP
  have hfFinContractive : ∀ T, ‖fFin T‖ ≤ ‖T‖ := by
    intro T
    refine (hfMatrixContractive (reindex.symm T)).trans_eq ?_
    exact NonUnitalStarAlgHom.norm_map
      reindex.symm.toStarAlgHom.toNonUnitalStarAlgHom reindex.symm.injective T
  obtain ⟨matrixLift, hmatrixLiftCP, hmatrixLiftContractive,
      hmatrixLift⟩ :=
    exists_completelyPositiveContractive_matrix_lift X fFin hfFinCP
      hfFinContractive
  let toFin : D →ₗ[ℂ] Matrix (Fin (Fintype.card R.model))
      (Fin (Fintype.card R.model)) ℂ :=
    (starAlgEquivLinearMap reindex).comp
      (R.embedding : D →ₗ[ℂ] Matrix R.model R.model ℂ)
  let lift : D →ₗ[ℂ] BoundedMatrixSequence X :=
    matrixLift.comp toFin
  have hembeddingCP : IsCompletelyPositive
      (R.embedding : D →ₗ[ℂ] Matrix R.model R.model ℂ) :=
    isCompletelyPositive_of_starAlgHom R.embedding.toNonUnitalStarAlgHom
  have hreindexCP : IsCompletelyPositive (starAlgEquivLinearMap reindex) :=
    isCompletelyPositive_of_starAlgHom
      reindex.toStarAlgHom.toNonUnitalStarAlgHom
  have htoFinCP : IsCompletelyPositive toFin :=
    hreindexCP.comp hembeddingCP
  refine ⟨lift, hmatrixLiftCP.comp htoFinCP, ?_, ?_⟩
  · intro d
    refine (hmatrixLiftContractive (toFin d)).trans_eq ?_
    calc
      ‖toFin d‖ = ‖reindex (R.embedding d)‖ := rfl
      _ = ‖R.embedding d‖ := NonUnitalStarAlgHom.norm_map
        reindex.toStarAlgHom.toNonUnitalStarAlgHom reindex.injective _
      _ = ‖d‖ := NonUnitalStarAlgHom.norm_map
        R.embedding.toNonUnitalStarAlgHom R.embedding_injective d
  · intro d
    dsimp only [lift, LinearMap.comp_apply]
    rw [hmatrixLift]
    change f (R.retract (reindex.symm (reindex (R.embedding d)))) = f d
    rw [reindex.symm_apply_apply]
    rw [R.retract_embedding]

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_completelyPositiveContractive_finiteDimensional_lift
