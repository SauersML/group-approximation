import GroupApproximation.Analysis.FiniteDirectSumMatrixCPRetract
import GroupApproximation.Analysis.FiniteProductCorrectedStarEquiv
import GroupApproximation.Meta.AxiomGuard

/-!
# Nontrivial finite-dimensional C-star algebras are matrix UCP retracts

The corrected C-star Wedderburn equivalence identifies a nontrivial
finite-dimensional complex C-star algebra with a nonempty finite product of
nonzero matrix blocks.  The finite-product UCP retract is transported across
that equivalence here, producing a single full matrix algebra with a unital
completely positive contractive retraction.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

local instance matrixBlockCStarAlgebraForFiniteDimensionalRetract
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance directMatrixSumCStarAlgebraForFiniteDimensionalRetract
    {I : Type} [Fintype I] [DecidableEq I]
    (d : I → ℕ) [∀ i, Nonempty (Fin (d i))] :
    CStarAlgebra (DirectMatrixSum d) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- A finite-dimensional unital complex C-star algebra is a UCP retract of
one full matrix algebra. -/
theorem exists_matrixUCPRetract_of_finiteDimensionalCStar
    (D : Type u) [CStarAlgebra D] [Nontrivial D] [FiniteDimensional ℂ D] :
    Nonempty (MatrixUCPRetract D) := by
  obtain ⟨r, d, hne, ⟨e⟩⟩ :=
    exists_starAlgEquiv_directMatrixSum_of_finiteDimensionalCStar D
  have hr : r ≠ 0 := by
    intro hr0
    subst r
    have himage : e (0 : D) = e 1 := by
      funext i
      exact i.elim0
    exact (zero_ne_one : (0 : D) ≠ 1) (e.injective himage)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  letI : ∀ i, Nonempty (Fin (d i)) := hne
  obtain ⟨R⟩ := exists_matrixUCPRetract_directMatrixSum_succ n d
  let ret : Matrix R.model R.model ℂ →ₗ[ℂ] D :=
    e.symm.toAlgEquiv.toLinearEquiv.toLinearMap.comp R.retract
  refine ⟨{
    model := R.model
    embedding := R.embedding.comp e.toStarAlgHom
    retract := ret
    retract_completelyPositive :=
      (isCompletelyPositive_of_starAlgHom
        e.symm.toStarAlgHom.toNonUnitalStarAlgHom).comp
          R.retract_completelyPositive
    retract_embedding := ?_
    retract_one := ?_ }⟩
  · intro x
    change e.symm (R.retract (R.embedding (e x))) = x
    rw [R.retract_embedding, e.symm_apply_apply]
  · change e.symm (R.retract 1) = 1
    rw [R.retract_one, map_one]

/-- Fully unpacked matrix UCP retract data for a finite-dimensional C-star
algebra, including the contractive estimate needed in CPAP/NF compositions. -/
theorem exists_matrix_ucp_retraction_of_finiteDimensionalCStar
    (D : Type u) [CStarAlgebra D] [Nontrivial D] [FiniteDimensional ℂ D] :
    ∃ (Y : Type) (hYf : Fintype Y) (hYd : DecidableEq Y)
      (hYn : Nonempty Y),
      letI : Fintype Y := hYf
      letI : DecidableEq Y := hYd
      letI : Nonempty Y := hYn
      ∃ (embedding : D →⋆ₐ[ℂ] Matrix Y Y ℂ)
        (retract : Matrix Y Y ℂ →ₗ[ℂ] D),
        IsCompletelyPositive retract ∧
          retract 1 = 1 ∧
          (∀ x, retract (embedding x) = x) ∧
          ∀ T, ‖retract T‖ ≤ ‖T‖ := by
  obtain ⟨R⟩ := exists_matrixUCPRetract_of_finiteDimensionalCStar D
  exact ⟨R.model, R.fintype, R.decidableEq, R.modelNonempty,
    R.embedding, R.retract, R.retract_completelyPositive, R.retract_one,
    R.retract_embedding, R.retract_norm_le⟩

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_matrixUCPRetract_of_finiteDimensionalCStar
#audit_axioms exists_matrix_ucp_retraction_of_finiteDimensionalCStar
