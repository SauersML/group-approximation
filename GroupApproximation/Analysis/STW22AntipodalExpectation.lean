import GroupApproximation.Analysis.AntipodalHomogeneousBlock
import GroupApproximation.Analysis.CStarCorestrictCP
import GroupApproximation.Analysis.CStarCPConvex

/-!
# The antipodal conditional expectation

The order-two action

`f(x) ↦ u f(-x) u`

on continuous matrix-valued sphere functions is an isometric star-algebra
automorphism.  Averaging it with the identity gives a completely positive
contractive retraction onto the antipodally covariant block.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open CStarExactness

noncomputable section

open scoped CStarAlgebra ComplexOrder Matrix

/-- A coherence-friendly presentation of the continuous-section C-star
structure.  Its inherited algebraic structures are the pointwise
`ContinuousMap` structures used by the explicit formulas below. -/
local instance sphereMatrixFunctionsCStarAlgebra (d s : ℕ) :
    CStarAlgebra (SphereMatrixFunctions d s) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance sphereMatrixFunctionsPartialOrder (d s : ℕ) :
    PartialOrder (SphereMatrixFunctions d s) :=
  CStarAlgebra.spectralOrder _

local instance sphereMatrixFunctionsStarOrderedRing (d s : ℕ) :
    StarOrderedRing (SphereMatrixFunctions d s) :=
  CStarAlgebra.spectralOrderedRing _

/-- The order-two star automorphism whose fixed points are the antipodal
block. -/
def antipodalActionEquiv (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    SphereMatrixFunctions d s ≃⋆ₐ[ℂ] SphereMatrixFunctions d s where
  toFun f :=
    ⟨fun x ↦ u * f (-x) * u,
      (continuous_const.mul (f.continuous.comp continuous_neg)).mul
        continuous_const⟩
  invFun f :=
    ⟨fun x ↦ u * f (-x) * u,
      (continuous_const.mul (f.continuous.comp continuous_neg)).mul
        continuous_const⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    change u * (u * f (- -x) * u) * u = f x
    rw [neg_neg]
    calc
      u * (u * f x * u) * u = (u * u) * f x * (u * u) := by
        noncomm_ring
      _ = f x := by rw [hu_sq]; simp
  right_inv f := by
    apply ContinuousMap.ext
    intro x
    change u * (u * f (- -x) * u) * u = f x
    rw [neg_neg]
    calc
      u * (u * f x * u) * u = (u * u) * f x * (u * u) := by
        noncomm_ring
      _ = f x := by rw [hu_sq]; simp
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    change u * (f (-x) + g (-x)) * u =
      u * f (-x) * u + u * g (-x) * u
    noncomm_ring
  map_mul' f g := by
    apply ContinuousMap.ext
    intro x
    change u * (f (-x) * g (-x)) * u =
      (u * f (-x) * u) * (u * g (-x) * u)
    calc
      u * (f (-x) * g (-x)) * u =
          u * f (-x) * (u * u) * g (-x) * u := by rw [hu_sq]; simp [mul_assoc]
      _ = (u * f (-x) * u) * (u * g (-x) * u) := by noncomm_ring
  map_smul' c f := by
    apply ContinuousMap.ext
    intro x
    change u * (c • f (-x)) * u = c • (u * f (-x) * u)
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  map_star' f := by
    apply ContinuousMap.ext
    intro x
    change u * star (f (-x)) * u = star (u * f (-x) * u)
    rw [star_mul, star_mul, hu_star]
    noncomm_ring

@[simp] theorem antipodalActionEquiv_apply (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (f : SphereMatrixFunctions d s) (x : Sphere d) :
    antipodalActionEquiv d s u hu_sq hu_star f x = u * f (-x) * u := rfl

/-- The ambient averaging map `(id + action)/2`. -/
def antipodalAverageLinearMap (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    SphereMatrixFunctions d s →ₗ[ℂ] SphereMatrixFunctions d s :=
  ((2 : ℂ)⁻¹) •
    (LinearMap.id +
      (antipodalActionEquiv d s u hu_sq hu_star).toStarAlgHom.toLinearMap)

@[simp] theorem antipodalAverageLinearMap_apply (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (f : SphereMatrixFunctions d s) (x : Sphere d) :
    antipodalAverageLinearMap d s u hu_sq hu_star f x =
      (2 : ℂ)⁻¹ • (f x + u * f (-x) * u) := by
  simp [antipodalAverageLinearMap, antipodalActionEquiv_apply]

/-- The antipodal average satisfies the covariance relation. -/
theorem antipodalAverage_isCovariant (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (f : SphereMatrixFunctions d s) :
    IsAntipodalCovariant u (antipodalAverageLinearMap d s u hu_sq hu_star f) := by
  intro x
  rw [antipodalAverageLinearMap_apply, antipodalAverageLinearMap_apply, neg_neg]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  symm
  calc
    u * (f x + u * f (-x) * u) * u =
        u * f x * u + (u * u) * f (-x) * (u * u) := by noncomm_ring
    _ = u * f x * u + f (-x) := by rw [hu_sq]; simp
    _ = f (-x) + u * f x * u := add_comm _ _

/-- The antipodal expectation, corestricted to the fixed-point block. -/
def antipodalExpectation (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    SphereMatrixFunctions d s →ₗ[ℂ] AntipodalBlock d s u hu_sq hu_star where
  toFun f := ⟨antipodalAverageLinearMap d s u hu_sq hu_star f,
    antipodalAverage_isCovariant d s u hu_sq hu_star f⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (antipodalAverageLinearMap d s u hu_sq hu_star) f g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (antipodalAverageLinearMap d s u hu_sq hu_star) c f

@[simp] theorem antipodalExpectation_coe (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (f : SphereMatrixFunctions d s) :
    ((antipodalExpectation d s u hu_sq hu_star f :
      AntipodalBlock d s u hu_sq hu_star) : SphereMatrixFunctions d s) =
      antipodalAverageLinearMap d s u hu_sq hu_star f := rfl

/-- The block inclusion. -/
def antipodalBlockInclusion (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    AntipodalBlock d s u hu_sq hu_star →⋆ₙₐ[ℂ] SphereMatrixFunctions d s :=
  (antipodalBlockStarSubalgebra d s u hu_sq hu_star).subtype.toNonUnitalStarAlgHom

/-- Averaging fixes every covariant section. -/
theorem antipodalExpectation_inclusion (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (f : AntipodalBlock d s u hu_sq hu_star) :
    antipodalExpectation d s u hu_sq hu_star
      (antipodalBlockInclusion d s u hu_sq hu_star f) = f := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rw [antipodalExpectation_coe, antipodalAverageLinearMap_apply]
  have hf := f.2 (-x)
  rw [neg_neg] at hf
  change (2 : ℂ)⁻¹ • (f.1 x + u * f.1 (-x) * u) = f.1 x
  rw [← hf]
  module

/-- The ambient antipodal average is completely positive. -/
theorem isCompletelyPositive_antipodalAverageLinearMap (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    IsCompletelyPositive (antipodalAverageLinearMap d s u hu_sq hu_star) := by
  have hid : IsCompletelyPositive
      (LinearMap.id : SphereMatrixFunctions d s →ₗ[ℂ] SphereMatrixFunctions d s) :=
    isCompletelyPositive_id
  have haction : IsCompletelyPositive
      (antipodalActionEquiv d s u hu_sq hu_star).toStarAlgHom.toLinearMap :=
    isCompletelyPositive_of_starAlgHom
      (antipodalActionEquiv d s u hu_sq hu_star).toStarAlgHom.toNonUnitalStarAlgHom
  simpa [antipodalAverageLinearMap] using
    (BlackadarKirchberg.CStarExactness.IsCompletelyPositive.add hid haction).nonnegativeReal_smul
      (1 / 2) (by norm_num)

/-- Corestricting the average to its closed fixed-point algebra preserves
complete positivity. -/
theorem isCompletelyPositive_antipodalExpectation (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) :
    IsCompletelyPositive (antipodalExpectation d s u hu_sq hu_star) := by
  classical
  intro n M hM
  obtain ⟨P, hPmem, hP⟩ :=
    exists_factor_entries_mem_of_isCompletelyPositive
      (antipodalBlockStarSubalgebra d s u hu_sq hu_star)
      (isClosed_antipodalBlockStarSubalgebra d s u hu_sq hu_star)
      (isCompletelyPositive_antipodalAverageLinearMap d s u hu_sq hu_star)
      (fun f ↦ antipodalAverage_isCovariant d s u hu_sq hu_star f) n M hM
  let Q : CStarMatrix (Fin n) (Fin n) (AntipodalBlock d s u hu_sq hu_star) :=
    fun i j ↦ ⟨P i j, hPmem i j⟩
  refine ⟨Q, ?_⟩
  apply CStarMatrix.ext
  intro i j
  apply Subtype.ext
  have hleft :
      (((M.map ⇑(antipodalExpectation d s u hu_sq hu_star)) i j :
          AntipodalBlock d s u hu_sq hu_star) : SphereMatrixFunctions d s) =
        (M.map ⇑(antipodalAverageLinearMap d s u hu_sq hu_star)) i j := rfl
  have hright :
      ((((star Q * Q) i j : AntipodalBlock d s u hu_sq hu_star) :
          SphereMatrixFunctions d s)) = (star P * P) i j := by
    rw [CStarMatrix.mul_apply, CStarMatrix.mul_apply]
    change (antipodalBlockStarSubalgebra d s u hu_sq hu_star).subtype
        (∑ x, star (Q x i) * Q x j) =
      ∑ x, star (P x i) * P x j
    rw [map_sum (antipodalBlockStarSubalgebra d s u hu_sq hu_star).subtype]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hleft, hright, hP]

/-- The fixed-point expectation is contractive. -/
theorem norm_antipodalExpectation_le (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (f : SphereMatrixFunctions d s) :
    ‖antipodalExpectation d s u hu_sq hu_star f‖ ≤ ‖f‖ := by
  change ‖antipodalAverageLinearMap d s u hu_sq hu_star f‖ ≤ ‖f‖
  rw [show antipodalAverageLinearMap d s u hu_sq hu_star f =
      (2 : ℂ)⁻¹ •
        (f + antipodalActionEquiv d s u hu_sq hu_star f) by rfl,
    norm_smul]
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar]
  calc
    (1 / 2 : ℝ) * ‖f + antipodalActionEquiv d s u hu_sq hu_star f‖ ≤
        (1 / 2 : ℝ) * (‖f‖ + ‖antipodalActionEquiv d s u hu_sq hu_star f‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖f‖ := by rw [StarAlgEquiv.norm_map]; ring

end

end STW22
end GroupApproximation
