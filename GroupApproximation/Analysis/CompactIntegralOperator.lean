import GroupApproximation.Analysis.CompactHaar
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Integral operators on a compact target

Step one of the route recorded in `Analysis/CompactHaar`: the convolution-type
operator, built so that the analysis stays inside what Mathlib already proves.

For `φ : C(C, ℂ)` the operator is

  `T_φ f x = ⟪k_φ x, f⟫`,   `k_φ x y = conj (φ (x⁻¹ * y))`,

which is the `L²` pairing form of `∫ φ (x⁻¹ y) f y`.  Writing it as a pairing
rather than an integral is what keeps the side conditions cheap: `k_φ` is
continuous on `C × C`, so currying gives a *continuous* map `x ↦ k_φ x` into
`C(C, ℂ)` with no uniform-continuity argument, and `ContinuousMap.toLp` carries
it into `L²` as a continuous linear map of norm at most one, Haar being a
probability measure.

`T_φ f` is then continuous in `x`, hence bounded on a compact space, hence back
in `L²` -- and the same bound `‖T_φ f‖₂ ≤ ‖φ‖_∞ ‖f‖₂` comes out of
Cauchy--Schwarz with nothing else assumed.
-/

namespace GroupApproximation
namespace PeterWeyl

open MeasureTheory Measure Complex
open scoped InnerProductSpace

variable (C : CompactTarget)

/-- Complex conjugation as a continuous map. -/
noncomputable def conjCM : C(ℂ, ℂ) := ⟨starRingEnd ℂ, continuous_star⟩

/-- The conjugated kernel, curried: `x ↦ (y ↦ conj (k (x, y)))`.  Currying needs
the second factor locally compact, which a compact Hausdorff group is. -/
noncomputable def kernelCurried (k : C(C.carrier × C.carrier, ℂ)) :
    C(C.carrier, C(C.carrier, ℂ)) :=
  (conjCM.comp k).curry

/-- The kernel slice at `x`, as an element of `L²`.  Pairing against it computes
`∫ k x y * f y`, the conjugation in `kernelCurried` cancelling the one in the
inner product. -/
noncomputable def kernelL2 (k : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    Lp ℂ 2 C.haar :=
  ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (kernelCurried C k x)

/-- **The kernel slice varies continuously in `L²`.**  Currying supplies
continuity into `C(C, ℂ)` and `ContinuousMap.toLp` is continuous, so no
uniform-continuity argument is needed. -/
theorem continuous_kernelL2 (k : C(C.carrier × C.carrier, ℂ)) :
    Continuous (kernelL2 C k) :=
  (ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ).continuous.comp
    (kernelCurried C k).continuous


/-- Haar on a compact target has total NNReal mass one. -/
@[simp] theorem measureUnivNNReal_haar : measureUnivNNReal C.haar = 1 := by
  simp [measureUnivNNReal, C.haar_univ]

/-- `ContinuousMap.toLp` into `L²` of a probability measure is a contraction. -/
theorem toLp_opNorm_le_one :
    ‖(ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ)‖ ≤ 1 := by
  refine le_trans (ContinuousMap.toLp_norm_le C.haar) ?_
  simp

/-- The kernel slice is bounded by the sup norm of `φ`. -/
theorem norm_kernelL2_le (k : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    ‖kernelL2 C k x‖ ≤ ‖k‖ := by
  have h3 : ‖kernelCurried C k x‖ ≤ ‖k‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun y => ?_
    have hval : ‖(kernelCurried C k x) y‖ = ‖k (x, y)‖ := by
      simp [kernelCurried, conjCM]
    rw [hval]
    exact k.norm_coe_le_norm _
  calc ‖kernelL2 C k x‖
      ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ)‖ * ‖kernelCurried C k x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖k‖ :=
        mul_le_mul (toLp_opNorm_le_one C) h3 (norm_nonneg _) zero_le_one
    _ = ‖k‖ := one_mul _


/-! ## The operator -/

/-- `T_φ f` as a continuous function of `x`: the `L²` pairing of `f` against the
kernel slice. -/
noncomputable def applyCM (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    C(C.carrier, ℂ) :=
  ⟨fun x => ⟪kernelL2 C k x, f⟫_ℂ,
    continuous_inner.comp ((continuous_kernelL2 C k).prodMk continuous_const)⟩

@[simp] theorem applyCM_apply (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar)
    (x : C.carrier) : applyCM C k f x = ⟪kernelL2 C k x, f⟫_ℂ := rfl

theorem norm_applyCM_le (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    ‖applyCM C k f‖ ≤ ‖k‖ * ‖f‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
  have hcs : ‖(⟪kernelL2 C k x, f⟫_ℂ : ℂ)‖ ≤ ‖kernelL2 C k x‖ * ‖f‖ := by
    simpa using norm_inner_le_norm (𝕜 := ℂ) (kernelL2 C k x) f
  have hx : applyCM C k f x = ⟪kernelL2 C k x, f⟫_ℂ := rfl
  rw [hx]
  exact hcs.trans (mul_le_mul_of_nonneg_right (norm_kernelL2_le C k x) (norm_nonneg _))

/-- **The integral operator.**  Bounded by the sup norm of `φ`, with no
hypothesis: Haar is a probability measure, so both `ContinuousMap.toLp` and the
Cauchy--Schwarz step are contractions. -/
noncomputable def integralOp (k : C(C.carrier × C.carrier, ℂ)) :
    Lp ℂ 2 C.haar →L[ℂ] Lp ℂ 2 C.haar :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (applyCM C k f)
      map_add' := by
        intro f g
        have h : applyCM C k (f + g) = applyCM C k f + applyCM C k g := by
          ext x; simp [inner_add_right]
        rw [h, map_add]
      map_smul' := by
        intro a f
        have h : applyCM C k (a • f) = a • applyCM C k f := by
          ext x; simp [inner_smul_right]
        rw [h, map_smul]
        rfl }
    ‖k‖
    (by
      intro f
      calc ‖ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (applyCM C k f)‖
          ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ)‖ * ‖applyCM C k f‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (‖k‖ * ‖f‖) :=
            mul_le_mul (toLp_opNorm_le_one C) (norm_applyCM_le C k f)
              (norm_nonneg _) zero_le_one
        _ = ‖k‖ * ‖f‖ := one_mul _)

theorem integralOp_apply (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    integralOp C k f = ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (applyCM C k f) :=
  rfl


/-! ## Dependence on the kernel

The two conjugations cancel, so `k ↦ T_k` is linear, and the sup-norm bound makes
it Lipschitz.  That is exactly what lets a uniform approximation of the kernel
become a norm approximation of the operator.
-/

theorem kernelCurried_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelCurried C (k₁ - k₂) x = kernelCurried C k₁ x - kernelCurried C k₂ x := by
  ext y; simp [kernelCurried, conjCM]

theorem kernelL2_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelL2 C (k₁ - k₂) x = kernelL2 C k₁ x - kernelL2 C k₂ x := by
  rw [kernelL2, kernelCurried_sub, map_sub]
  rfl

theorem applyCM_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    applyCM C (k₁ - k₂) f = applyCM C k₁ f - applyCM C k₂ f := by
  ext x
  simp [applyCM_apply, kernelL2_sub, inner_sub_left]

theorem integralOp_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) :
    integralOp C (k₁ - k₂) = integralOp C k₁ - integralOp C k₂ := by
  ext f
  simp [integralOp_apply, applyCM_sub, map_sub]

/-- The operator norm is bounded by the sup norm of the kernel. -/
theorem norm_integralOp_le (k : C(C.carrier × C.carrier, ℂ)) :
    ‖integralOp C k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- **Uniform convergence of kernels gives norm convergence of operators.** -/
theorem norm_integralOp_sub_le (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) :
    ‖integralOp C k₁ - integralOp C k₂‖ ≤ ‖k₁ - k₂‖ := by
  rw [← integralOp_sub]
  exact norm_integralOp_le C _

end PeterWeyl
end GroupApproximation
