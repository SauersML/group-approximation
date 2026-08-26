import GroupApproximation.Analysis.BlackadarKirchbergFiniteDirectSumLift
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Transporting finite-dimensional matrix lifts across star equivalences

This file isolates the formal consequence of a star-compatible
finite-dimensional structure theorem.  A star-algebra equivalence is
completely positive in both directions and isometric, so the exact c.p.c.
lifting theorem for a finite product of matrix blocks transports back to the
original C-star algebra.

The theorem below does not assert that an arbitrary algebraic Wedderburn
equivalence preserves `star`.  Constructing a star-compatible equivalence is
the remaining structure-theorem step.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open scoped CStarAlgebra Matrix.Norms.L2Operator

universe u v

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (d : I → ℕ) [∀ i, Nonempty (Fin (d i))]
variable (X : ℕ → Type u) [∀ n, Fintype (X n)]
  [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]

local instance directMatrixBlockCStarAlgebraForTransport (i : I) :
    CStarAlgebra (Matrix (Fin (d i)) (Fin (d i)) ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance directMatrixSumCStarAlgebraForTransport :
    CStarAlgebra (DirectMatrixSum d) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance boundedMatrixSequenceCStarAlgebraForTransport :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Precomposition by a star-algebra equivalence preserves complete
positivity. -/
theorem isCompletelyPositive_comp_starAlgEquiv
    {A : Type v} {B C : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (e : A ≃⋆ₐ[ℂ] B) (f : B →ₗ[ℂ] C)
    (hf : CStarExactness.IsCompletelyPositive f) :
    CStarExactness.IsCompletelyPositive
      (f.comp e.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap) := by
  apply hf.comp
  intro n M hM
  obtain ⟨N, hN⟩ := hM
  let e★ := e.toStarAlgHom.toNonUnitalStarAlgHom
  refine ⟨CStarMatrix.mapₙₐ (n := Fin n) e★ N, ?_⟩
  have hmap :
      M.map ⇑e.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap =
        CStarMatrix.mapₙₐ (n := Fin n) e★ M := by
    ext i j
    rfl
  rw [hmap, hN, map_mul, map_star]

/-- Exact c.p.c. matrix-corona lifts transport across a star-algebra
equivalence with an explicit finite product of full matrix algebras. -/
theorem exists_completelyPositiveContractive_lift_of_starAlgEquiv_directMatrixSum
    {D : Type v} [CStarAlgebra D]
    (e : D ≃⋆ₐ[ℂ] DirectMatrixSum d)
    (f : D →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f)
    (hcontract : ∀ x, ‖f x‖ ≤ ‖x‖) :
    ∃ lift : D →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      (∀ x, ‖lift x‖ ≤ ‖x‖) ∧
      ∀ x, normMatrixCStarCoronaQuotient X (lift x) = f x := by
  let einv : DirectMatrixSum d →ₗ[ℂ] D :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap
  let pushed : DirectMatrixSum d →ₗ[ℂ] NormMatrixCStarCorona X :=
    f.comp einv
  have hpushed : CStarExactness.IsCompletelyPositive pushed := by
    exact isCompletelyPositive_comp_starAlgEquiv e.symm f hf
  have hpushedContract : ∀ y, ‖pushed y‖ ≤ ‖y‖ := by
    intro y
    change ‖f (einv y)‖ ≤ ‖y‖
    calc
      ‖f (einv y)‖ ≤ ‖einv y‖ := hcontract (einv y)
      _ = ‖y‖ := by
        simpa only [einv] using StarAlgEquiv.norm_map e.symm y
  obtain ⟨matrixLift, hmatrixCP, hmatrixContract, hmatrixQuot⟩ :=
    exists_completelyPositiveContractive_directMatrixSum_lift
      d X pushed hpushed hpushedContract
  let edir : D →ₗ[ℂ] DirectMatrixSum d :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap
  let lift : D →ₗ[ℂ] BoundedMatrixSequence X := matrixLift.comp edir
  refine ⟨lift, ?_, ?_, ?_⟩
  · exact isCompletelyPositive_comp_starAlgEquiv e matrixLift hmatrixCP
  · intro x
    change ‖matrixLift (edir x)‖ ≤ ‖x‖
    calc
      ‖matrixLift (edir x)‖ ≤ ‖edir x‖ := hmatrixContract (edir x)
      _ = ‖x‖ := by simpa only [edir] using StarAlgEquiv.norm_map e x
  · intro x
    calc
      normMatrixCStarCoronaQuotient X (lift x) = pushed (edir x) :=
        hmatrixQuot (edir x)
      _ = f x := by simp [pushed, einv, edir]

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms isCompletelyPositive_comp_starAlgEquiv
#audit_axioms exists_completelyPositiveContractive_lift_of_starAlgEquiv_directMatrixSum
