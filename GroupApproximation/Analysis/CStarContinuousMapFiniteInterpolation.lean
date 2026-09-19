import GroupApproximation.Analysis.BlackadarKirchbergFiniteDirectSumLift
import GroupApproximation.Analysis.CStarCPConjugation
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# Finite completely positive interpolation on compact continuous-map algebras

For finitely many sample points, evaluation is a contractive star homomorphism
into a finite product.  A nonnegative continuous partition of unity gives a
contractive completely positive interpolation map in the other direction.
These are the algebraic maps used in the direct CPAP proof for sphere-valued
matrix functions.
-/

namespace GroupApproximation
namespace CStarContinuousMapFiniteInterpolation

open CStarExactness BlackadarKirchberg

noncomputable section

set_option linter.unusedSectionVars false

universe u v

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
variable {B : Type v} [CStarAlgebra B]

/-- Simultaneous evaluation at finitely many points. -/
def finiteEvaluationStarAlgHom {k : ℕ} (x : Fin k → X) :
    C(X, B) →⋆ₐ[ℂ] (∀ _ : Fin k, B) where
  toFun f i := f (x i)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem finiteEvaluationStarAlgHom_apply {k : ℕ} (x : Fin k → X)
    (f : C(X, B)) (i : Fin k) :
    finiteEvaluationStarAlgHom x f i = f (x i) := rfl

/-- Finite evaluation is contractive for the supremum norm. -/
theorem norm_finiteEvaluationStarAlgHom_le {k : ℕ} (x : Fin k → X)
    (f : C(X, B)) : ‖finiteEvaluationStarAlgHom x f‖ ≤ ‖f‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg f)]
  intro i
  exact ContinuousMap.norm_coe_le_norm f (x i)

/-- The constant-section star homomorphism. -/
def constantSectionStarAlgHom : B →⋆ₐ[ℂ] C(X, B) where
  toFun b := ContinuousMap.const X b
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem constantSectionStarAlgHom_apply (b : B) (y : X) :
    constantSectionStarAlgHom (X := X) b y = b := rfl

/-- A real nonnegative weight, regarded as a central square-root section. -/
def weightSqrtSection (w : C(X, ℝ)) : C(X, B) where
  toFun y := algebraMap ℂ B (Real.sqrt (w y))
  continuous_toFun := (continuous_algebraMap ℂ B).comp
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp w.continuous))

@[simp] theorem weightSqrtSection_apply (w : C(X, ℝ)) (y : X) :
    weightSqrtSection (B := B) w y = algebraMap ℂ B (Real.sqrt (w y)) := rfl

/-- The `i`-th weighted constant section, written as a CP conjugation of the
coordinate projection followed by the constant-section homomorphism. -/
def weightedCoordinateLinearMap {k : ℕ} (w : Fin k → C(X, ℝ)) (i : Fin k) :
    (∀ _ : Fin k, B) →ₗ[ℂ] C(X, B) :=
  conjugationLinearMap (weightSqrtSection (B := B) (w i)) ∘ₗ
    ((constantSectionStarAlgHom (X := X)).comp
      (Pi.evalStarAlgHom ℂ (fun _ : Fin k ↦ B) i)).toLinearMap

/-- The weighted-coordinate formula after evaluating at a point. -/
theorem weightedCoordinateLinearMap_apply {k : ℕ} (w : Fin k → C(X, ℝ))
    (hw : ∀ i y, 0 ≤ w i y) (i : Fin k) (a : ∀ _ : Fin k, B) (y : X) :
    weightedCoordinateLinearMap (B := B) w i a y = (w i y : ℂ) • a i := by
  simp only [weightedCoordinateLinearMap, LinearMap.coe_comp, Function.comp_apply,
    conjugationLinearMap_apply]
  let r : ℝ := Real.sqrt (w i y)
  have hr : r * r = w i y := Real.mul_self_sqrt (hw i y)
  change star (algebraMap ℂ B (r : ℂ)) * a i *
      algebraMap ℂ B (r : ℂ) = (w i y : ℂ) • a i
  rw [show star (algebraMap ℂ B (r : ℂ)) =
      algebraMap ℂ B (r : ℂ) by
        rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
        simp]
  calc
    algebraMap ℂ B (r : ℂ) * a i * algebraMap ℂ B (r : ℂ) =
        (algebraMap ℂ B (r : ℂ) * algebraMap ℂ B (r : ℂ)) * a i := by
          rw [mul_assoc, ← Algebra.commutes (r : ℂ) (a i), ← mul_assoc]
    _ = algebraMap ℂ B (w i y : ℂ) * a i := by
      rw [← map_mul]
      congr 2
      exact_mod_cast hr
    _ = (w i y : ℂ) • a i := by rw [Algebra.smul_def]

/-- Every weighted-coordinate map is completely positive. -/
theorem isCompletelyPositive_weightedCoordinateLinearMap {k : ℕ}
    (w : Fin k → C(X, ℝ)) (i : Fin k) :
    IsCompletelyPositive (weightedCoordinateLinearMap (B := B) w i) :=
  (isCompletelyPositive_conjugationLinearMap
    (weightSqrtSection (B := B) (w i))).comp
      (isCompletelyPositive_of_starAlgHom
        ((constantSectionStarAlgHom (X := X)).comp
          (Pi.evalStarAlgHom ℂ (fun _ : Fin k ↦ B) i)).toNonUnitalStarAlgHom)

/-- Partition-of-unity interpolation from a finite product into continuous
sections. -/
def finiteInterpolation {k : ℕ} (w : Fin k → C(X, ℝ)) :
    (∀ _ : Fin k, B) →ₗ[ℂ] C(X, B) :=
  ∑ i, weightedCoordinateLinearMap (B := B) w i

theorem finiteInterpolation_apply {k : ℕ} (w : Fin k → C(X, ℝ))
    (hw : ∀ i y, 0 ≤ w i y) (a : ∀ _ : Fin k, B) (y : X) :
    finiteInterpolation (B := B) w a y = ∑ i, (w i y : ℂ) • a i := by
  simp only [finiteInterpolation, LinearMap.sum_apply, ContinuousMap.sum_apply,
    weightedCoordinateLinearMap_apply w hw]

/-- Partition-of-unity interpolation is completely positive. -/
theorem isCompletelyPositive_finiteInterpolation {k : ℕ}
    (w : Fin k → C(X, ℝ)) :
    IsCompletelyPositive (finiteInterpolation (B := B) w) :=
  isCompletelyPositive_finsetSum _
    (isCompletelyPositive_weightedCoordinateLinearMap (B := B) w)

/-- A nonnegative partition of unity makes interpolation contractive. -/
theorem norm_finiteInterpolation_le {k : ℕ} (w : Fin k → C(X, ℝ))
    (hw : ∀ i y, 0 ≤ w i y) (hsum : ∀ y, ∑ i, w i y = 1)
    (a : ∀ _ : Fin k, B) :
    ‖finiteInterpolation (B := B) w a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg a)).2
  intro y
  rw [finiteInterpolation_apply w hw]
  calc
    ‖∑ i, (w i y : ℂ) • a i‖ ≤ ∑ i, ‖(w i y : ℂ) • a i‖ :=
      norm_sum_le _ _
    _ = ∑ i, w i y * ‖a i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i y)]
    _ ≤ ∑ i, w i y * ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        ((pi_norm_le_iff_of_nonneg (norm_nonneg a)).1 le_rfl i) (hw i y)
    _ = ‖a‖ := by rw [← Finset.sum_mul, hsum y, one_mul]

end

end CStarContinuousMapFiniteInterpolation
end GroupApproximation
