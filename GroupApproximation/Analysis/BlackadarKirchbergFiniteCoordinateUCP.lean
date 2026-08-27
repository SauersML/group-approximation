import GroupApproximation.Analysis.CStarCPConvex
import GroupApproximation.Analysis.FiniteDimensionalCStarMatrixCPRetract
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite-coordinate UCP maps on a bounded matrix product

This module packages the concrete maps used by the finite-coordinate
localization step in the Blackadar--Kirchberg converse.  A finite convex
combination of completely positive maps applied at selected matrix
coordinates is completely positive.  If the component maps are unital and
the weights sum to one, the combination is unital and hence contractive.

The construction is deliberately on the bounded matrix numerator.  Its last
theorem records the exact finite-coordinate factorization property: two
sequences agreeing on the selected coordinates have the same image.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u w

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable {D : Type w} [CStarAlgebra D]

local instance matrixBlockCStarAlgebraForFiniteCoordinateUCP
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance boundedMatrixSequenceCStarAlgebraForFiniteCoordinateUCP :
    CStarAlgebra (BoundedMatrixSequence (fun n ↦ X n)) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

/-- A finite convex combination of maps evaluated at selected matrix
coordinates. -/
def finiteCoordinateConvexMap (S : Finset ℕ) (weight : S → ℝ)
    (component : ∀ n : S, Matrix (X n) (X n) ℂ →ₗ[ℂ] D) :
    BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] D :=
  ∑ n : S, (weight n : ℂ) •
    ((component n).comp (coordinateEvaluation (fun n ↦ X n) n))

@[simp] theorem finiteCoordinateConvexMap_apply (S : Finset ℕ)
    (weight : S → ℝ)
    (component : ∀ n : S, Matrix (X n) (X n) ℂ →ₗ[ℂ] D)
    (x : BoundedMatrixSequence (fun n ↦ X n)) :
    finiteCoordinateConvexMap S weight component x =
      ∑ n : S, (weight n : ℂ) • component n (x n) := by
  simp [finiteCoordinateConvexMap]

/-- Nonnegative finite coordinate combinations preserve complete
positivity. -/
theorem isCompletelyPositive_finiteCoordinateConvexMap
    (S : Finset ℕ) (weight : S → ℝ) (hweight : ∀ n, 0 ≤ weight n)
    (component : ∀ n : S, Matrix (X n) (X n) ℂ →ₗ[ℂ] D)
    (hcomponent : ∀ n : S,
      IsCompletelyPositive (A := Matrix (X n) (X n) ℂ) (B := D)
        (component n)) :
    IsCompletelyPositive
      (A := BoundedMatrixSequence (fun n ↦ X n)) (B := D)
      (finiteCoordinateConvexMap S weight component) := by
  unfold finiteCoordinateConvexMap
  apply isCompletelyPositive_finsetSum
  intro n
  exact (hcomponent n).comp
    (isCompletelyPositive_coordinateEvaluation (fun n ↦ X n) n) |>.nonnegativeReal_smul
      (weight n) (hweight n)

/-- A convex combination of unital coordinate maps is unital. -/
theorem finiteCoordinateConvexMap_one
    (S : Finset ℕ) (weight : S → ℝ)
    (hweight : ∑ n, weight n = 1)
    (component : ∀ n : S, Matrix (X n) (X n) ℂ →ₗ[ℂ] D)
    (hcomponent : ∀ n, component n 1 = 1) :
    finiteCoordinateConvexMap S weight component 1 = 1 := by
  rw [finiteCoordinateConvexMap_apply]
  have honeval : ∀ n : S,
      (1 : BoundedMatrixSequence (fun n ↦ X n)) n = 1 := by
    intro n
    rfl
  calc
    (∑ n : S, (weight n : ℂ) •
        component n ((1 : BoundedMatrixSequence (fun n ↦ X n)) n)) =
        ∑ n : S, (weight n : ℂ) • component n 1 := by
      exact Finset.sum_congr rfl fun n _ ↦ by rw [honeval n]
    _ = ∑ n : S, (weight n : ℂ) • (1 : D) := by
      exact Finset.sum_congr rfl fun n _ ↦ by rw [hcomponent n]
    _ = 1 := by
      rw [← Finset.sum_smul]
      simp only [← Complex.ofReal_sum, hweight, Complex.ofReal_one, one_smul]

/-- A finite convex coordinate UCP map into a nontrivial finite-dimensional
C-star algebra is contractive. -/
theorem finiteCoordinateConvexMap_norm_le
    [Nontrivial D] [FiniteDimensional ℂ D]
    (S : Finset ℕ) (weight : S → ℝ) (hweight0 : ∀ n, 0 ≤ weight n)
    (hweight1 : ∑ n, weight n = 1)
    (component : ∀ n : S, Matrix (X n) (X n) ℂ →ₗ[ℂ] D)
    (hcomponentCP : ∀ n : S,
      IsCompletelyPositive (A := Matrix (X n) (X n) ℂ) (B := D)
        (component n))
    (hcomponentOne : ∀ n, component n 1 = 1)
    (x : BoundedMatrixSequence (fun n ↦ X n)) :
    ‖finiteCoordinateConvexMap S weight component x‖ ≤ ‖x‖ := by
  obtain ⟨R⟩ := exists_matrixUCPRetract_of_finiteDimensionalCStar D
  let included : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ]
      Matrix R.model R.model ℂ :=
    (R.embedding : D →ₗ[ℂ] Matrix R.model R.model ℂ).comp
      (finiteCoordinateConvexMap S weight component)
  have hembeddingCP : IsCompletelyPositive
      (A := D) (B := Matrix R.model R.model ℂ)
      (R.embedding : D →ₗ[ℂ] Matrix R.model R.model ℂ) :=
    isCompletelyPositive_of_starAlgHom R.embedding.toNonUnitalStarAlgHom
  have hfiniteCP :=
    isCompletelyPositive_finiteCoordinateConvexMap S weight hweight0
      component hcomponentCP
  have hincludedCP : IsCompletelyPositive included :=
    hembeddingCP.comp hfiniteCP
  have hincludedOne : included 1 = 1 := by
    calc
      included 1 = R.embedding
          (finiteCoordinateConvexMap S weight component 1) := rfl
      _ = R.embedding 1 := by
        rw [finiteCoordinateConvexMap_one S weight hweight1 component hcomponentOne]
      _ = 1 := R.embedding.map_one
  let op : Matrix R.model R.model ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ R.model →L[ℂ] EuclideanSpace ℂ R.model) :=
    (Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom
  let includedOp := op.comp included
  have hopCP : IsCompletelyPositive op :=
    isCompletelyPositive_of_starAlgHom
      (Matrix.toEuclideanCLM (n := R.model)
        (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom
  have hincludedOpCP : IsCompletelyPositive includedOp :=
    hopCP.comp hincludedCP
  have hincludedOpOne : includedOp 1 = 1 := by
    dsimp only [includedOp, LinearMap.comp_apply]
    rw [hincludedOne]
    exact map_one (Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ))
  have hcontract :=
    hincludedOpCP.norm_apply_le_of_unital hincludedOpOne x
  calc
    ‖finiteCoordinateConvexMap S weight component x‖ =
        ‖R.embedding (finiteCoordinateConvexMap S weight component x)‖ :=
      (NonUnitalStarAlgHom.norm_map R.embedding.toNonUnitalStarAlgHom
        R.embedding_injective _).symm
    _ = ‖included x‖ := rfl
    _ = ‖includedOp x‖ := by
      change ‖included x‖ =
        ‖Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ) (included x)‖
      exact (Matrix.l2_opNorm_toEuclideanCLM (included x)).symm
    _ ≤ ‖x‖ := hcontract

/-- The map depends only on the selected finite set of coordinates. -/
theorem finiteCoordinateConvexMap_eq_of_selected_eq
    (S : Finset ℕ) (weight : S → ℝ)
    (component : ∀ n : S, Matrix (X n) (X n) ℂ →ₗ[ℂ] D)
    {x y : BoundedMatrixSequence (fun n ↦ X n)}
    (hxy : ∀ n : S, x n = y n) :
    finiteCoordinateConvexMap S weight component x =
      finiteCoordinateConvexMap S weight component y := by
  simp only [finiteCoordinateConvexMap_apply]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [hxy n]

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms isCompletelyPositive_finiteCoordinateConvexMap
#audit_axioms finiteCoordinateConvexMap_one
#audit_axioms finiteCoordinateConvexMap_norm_le
#audit_axioms finiteCoordinateConvexMap_eq_of_selected_eq
