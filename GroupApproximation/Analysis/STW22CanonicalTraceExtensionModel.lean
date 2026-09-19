import GroupApproximation.Analysis.STW22CanonicalTraceExtensionApproximationMultiplication

/-!
# Canonical trace extension on the concrete model

This file is one stage of the construction of the canonical extension of base
traces to the bounded uniform-two completion.
-/

namespace GroupApproximation
namespace STW22CanonicalTraceExtension

open scoped ComplexOrder

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open UniformTracialBoundedCauchyQuotient
open UniformTracialGNSTwoGauge STW22Assembly
open STW22ActualTraceSpaces STW22BaseUniformTracialGauge

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))]

/-! ## The extended tracial state on `ℂ1 + J` -/

private theorem extensionValue_zero (tau : TracialState (BaseAlgebra D)) :
    extensionValue tau (0 : M D) = 0 := by
  exact tendsto_nhds_unique
    (trace_tendsto_extensionValue tau 0 BaseApproximation.zero)
    (by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)) using 1
      all_goals simp [BaseApproximation.zero])

private theorem extensionValue_one (tau : TracialState (BaseAlgebra D)) :
    extensionValue tau (1 : M D) = 1 := by
  exact tendsto_nhds_unique
    (trace_tendsto_extensionValue tau 1 BaseApproximation.one)
    (by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)) using 1
      all_goals simp [BaseApproximation.one])

private theorem extensionValue_add (tau : TracialState (BaseAlgebra D))
    (x y : M D) : extensionValue tau (x + y) =
      extensionValue tau x + extensionValue tau y := by
  let A := chosenApproximation x
  let B := chosenApproximation y
  have hleft := trace_tendsto_extensionValue tau (x + y) (A.add B)
  have hright := (chosen_trace_tendsto tau x).add (chosen_trace_tendsto tau y)
  exact tendsto_nhds_unique hleft
    (by simpa [BaseApproximation.add] using hright)

private theorem extensionValue_smul (tau : TracialState (BaseAlgebra D))
    (c : ℂ) (x : M D) : extensionValue tau (c • x) =
      c • extensionValue tau x := by
  let A := chosenApproximation x
  have hleft := trace_tendsto_extensionValue tau (c • x) (A.smul c)
  have hright := (chosen_trace_tendsto tau x).const_smul c
  exact tendsto_nhds_unique hleft
    (by simpa [BaseApproximation.smul] using hright)

private theorem extensionValue_star_mul_self_nonneg
    (tau : TracialState (BaseAlgebra D)) (x : M D) :
    0 ≤ extensionValue tau (Star.star x * x) := by
  let A := chosenApproximation x
  have hlim := trace_tendsto_extensionValue tau
    (Star.star x * x) (A.star.mul A)
  exact ge_of_tendsto' hlim (fun k ↦ by
    simpa [BaseApproximation.mul, BaseApproximation.star] using
      tau.map_star_mul_self_nonneg (A.seq k))

private theorem extensionValue_mul_comm
    (tau : TracialState (BaseAlgebra D)) (x y : M D) :
    extensionValue tau (x * y) = extensionValue tau (y * x) := by
  let A := chosenApproximation x
  let B := chosenApproximation y
  have hxy := trace_tendsto_extensionValue tau (x * y) (A.mul B)
  have hyx := trace_tendsto_extensionValue tau (y * x) (B.mul A)
  change Tendsto (fun k ↦ tau (A.seq k * B.seq k)) atTop
    (nhds (extensionValue tau (x * y))) at hxy
  change Tendsto (fun k ↦ tau (B.seq k * A.seq k)) atTop
    (nhds (extensionValue tau (y * x))) at hyx
  have heq : (fun k ↦ tau (A.seq k * B.seq k)) =
      fun k ↦ tau (B.seq k * A.seq k) := by
    funext k
    exact tau.map_mul_comm _ _
  rw [heq] at hxy
  exact tendsto_nhds_unique hxy hyx

/-- The canonical uniform-two-continuous extension on the concrete model
`M = ℂ1 + J`. -/
noncomputable def modelExtension
    (tau : TracialState (BaseAlgebra D)) : TracialState (M D) where
  toLinearMap :=
    { toFun := extensionValue tau
      map_add' := extensionValue_add tau
      map_smul' := extensionValue_smul tau }
  map_one := extensionValue_one tau
  map_star_mul_self_nonneg := extensionValue_star_mul_self_nonneg tau
  map_mul_comm := extensionValue_mul_comm tau

@[simp] theorem modelExtension_baseToScalarPlusJ_apply
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    modelExtension tau (baseToScalarPlusJ (G D) x) = tau x := by
  let A : BaseApproximation (baseToScalarPlusJ (G D) x) :=
    { seq := fun _ ↦ x
      norm_bounded := ⟨‖x‖, fun _ ↦ le_rfl⟩
      tendsto_two := by
        have hfun : (fun _ : ℕ ↦ uniformTwoNorm (G D)
            (((baseToScalarPlusJ (G D) x : M D) -
              baseToScalarPlusJ (G D) x : M D) : BoundedCStarSequence D)) =
            fun _ ↦ (0 : ℝ) := by
          funext k
          simp only [sub_self]
          exact uniformTwoNorm_zero
        rw [hfun]
        exact tendsto_const_nhds }
  exact tendsto_nhds_unique
    (trace_tendsto_extensionValue tau _ A) (by simpa using tendsto_const_nhds)

private theorem norm_modelExtension_le_uniformTwoNorm
    (tau : TracialState (BaseAlgebra D)) (x : M D) :
    ‖modelExtension tau x‖ ≤ uniformTwoNorm (G D) x.1 := by
  let A := chosenApproximation x
  have hleft : Tendsto (fun k ↦ ‖tau (A.seq k)‖) atTop
      (nhds ‖modelExtension tau x‖) := (chosen_trace_tendsto tau x).norm
  have hright : Tendsto (fun k ↦
      uniformTwoNorm (G D)
          ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D) + uniformTwoNorm (G D) x.1)
      atTop (nhds (uniformTwoNorm (G D) x.1)) := by
    simpa using A.tendsto_two.add tendsto_const_nhds
  refine le_of_tendsto_of_tendsto' hleft hright (fun k ↦ ?_)
  calc
    ‖tau (A.seq k)‖ ≤ uniformTwoNorm (G D) (A.seq k).1 :=
      norm_trace_le_uniformTwoNorm tau _
    _ ≤ uniformTwoNorm (G D)
          ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D) + uniformTwoNorm (G D) x.1 := by
      calc
        uniformTwoNorm (G D) (A.seq k).1 =
            uniformTwoNorm (G D)
              ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 - 0) := by
          change uniformTwoNorm (G D) (A.seq k).1 =
            uniformTwoNorm (G D) ((A.seq k).1 - 0)
          rw [sub_zero]
        _ ≤ uniformTwoNorm (G D)
              ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 - x.1) +
            uniformTwoNorm (G D) (x.1 - 0) :=
          uniformTwoNorm_sub_triangle _ _ _
        _ = uniformTwoNorm (G D)
              ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
                BoundedCStarSequence D) + uniformTwoNorm (G D) x.1 := by
          rw [uniformTwoNorm_sub_comm, coe_sub_M, sub_zero]

/-- The model extension is sequentially continuous for the uniform
two-seminorm. -/
theorem modelExtension_isUniformTwoContinuous
    (tau : TracialState (BaseAlgebra D)) :
    IsUniformTwoContinuous (G D) (modelExtension tau) := by
  intro x hx
  refine squeeze_zero_norm (fun N ↦ ?_) hx
  exact norm_modelExtension_le_uniformTwoNorm tau (x N)

end

end STW22CanonicalTraceExtension
end GroupApproximation
