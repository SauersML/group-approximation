import GroupApproximation.Analysis.CStarStinespringDefect
import GroupApproximation.Analysis.CStarStinespringMul
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The dilation operators on the Stinespring space

## What this module provides

Each `c : A` acts on the dilation pre-space boundedly
(`CStarStinespringDefect`), so it extends to a bounded operator on the
completion.  This module performs the extension and carries the three
laws of `CStarStinespringMul` across it by density:

* `stinespringActCLM`, `stinespringRepOp` -- the operator, on the
  pre-space and on the completion, with `‖·‖ ≤ ‖c‖`;
* `stinespringRepOp_one`, `stinespringRepOp_mul` -- unit and
  multiplicativity;
* `inner_stinespringRepOp_adjoint` -- `star c` acts as the adjoint.

Additivity of `c ↦ π(c)` is *not* provable on the free model -- the
translated families differ as finitely supported functions -- and holds
on the completion only because the difference is a null vector of the
form.  That computation is the next module, not this one.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open UniformSpace

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (φ : A →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositive φ)

/-- The action of `c` on the pre-space, as a bounded operator. -/
noncomputable def stinespringActCLM (c : A) :
    StinespringPre φ hφ →L[ℂ] StinespringPre φ hφ :=
  LinearMap.mkContinuous (stinespringActPre φ hφ c) ‖c‖
    (norm_stinespringActPre_le_norm φ hφ c)

@[simp] theorem stinespringActCLM_apply (c : A) (f : StinespringPre φ hφ) :
    stinespringActCLM φ hφ c f = stinespringActPre φ hφ c f := rfl

/-- **The dilation operator**: the action of `c`, extended to the
Stinespring space. -/
noncomputable def stinespringRepOp (c : A) :
    StinespringSpace φ hφ →L[ℂ] StinespringSpace φ hφ :=
  (stinespringActCLM φ hφ c).completion

@[simp] theorem stinespringRepOp_coe (c : A) (f : StinespringPre φ hφ) :
    stinespringRepOp φ hφ c (f : StinespringSpace φ hφ)
      = ((stinespringActCLM φ hφ c f : StinespringPre φ hφ) :
          StinespringSpace φ hφ) :=
  ContinuousLinearMap.completion_apply_coe _ _

theorem stinespringRepOp_one :
    stinespringRepOp φ hφ (1 : A)
      = ContinuousLinearMap.id ℂ (StinespringSpace φ hφ) := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (stinespringRepOp φ hφ 1).continuous
        (ContinuousLinearMap.id ℂ _).continuous
  | ih f =>
      rw [stinespringRepOp_coe, ContinuousLinearMap.id_apply]
      have h : stinespringActCLM φ hφ 1 f = f := by
        rw [stinespringActCLM_apply, stinespringActPre_apply,
          stinespringActFree_one]
        rfl
      rw [h]

theorem stinespringRepOp_mul (c₁ c₂ : A) :
    stinespringRepOp φ hφ (c₁ * c₂)
      = (stinespringRepOp φ hφ c₁).comp (stinespringRepOp φ hφ c₂) := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (stinespringRepOp φ hφ (c₁ * c₂)).continuous
        ((stinespringRepOp φ hφ c₁).comp
          (stinespringRepOp φ hφ c₂)).continuous
  | ih f =>
      rw [ContinuousLinearMap.comp_apply, stinespringRepOp_coe,
        stinespringRepOp_coe, stinespringRepOp_coe]
      have h : stinespringActCLM φ hφ (c₁ * c₂) f
          = stinespringActCLM φ hφ c₁ (stinespringActCLM φ hφ c₂ f) := by
        rw [stinespringActCLM_apply, stinespringActCLM_apply,
          stinespringActCLM_apply, stinespringActPre_apply,
          stinespringActPre_apply, stinespringActPre_apply,
          stinespringActFree_mul]
        rfl
      rw [h]

/-- **The adjoint law on the pre-space**, in inner-product form. -/
theorem inner_stinespringActCLM_adjoint (c : A)
    (f g : StinespringPre φ hφ) :
    ⟪stinespringActCLM φ hφ c f, g⟫_ℂ
      = ⟪f, stinespringActCLM φ hφ (star c) g⟫_ℂ := by
  rw [stinespringPre_inner_def, stinespringPre_inner_def]
  exact stinespringSesq_act_adjoint c _ _

/-- **The adjoint law on the Stinespring space**: `star c` acts as the
adjoint of `c`. -/
theorem inner_stinespringRepOp_adjoint (c : A)
    (ζ η : StinespringSpace φ hφ) :
    ⟪stinespringRepOp φ hφ c ζ, η⟫_ℂ
      = ⟪ζ, stinespringRepOp φ hφ (star c) η⟫_ℂ := by
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact (continuous_inner.comp
          (((stinespringRepOp φ hφ c).continuous).prodMk
            continuous_const))
      · exact (continuous_inner.comp
          (continuous_id.prodMk continuous_const))
  | ih f =>
      induction η using UniformSpace.Completion.induction_on with
      | hp =>
          refine isClosed_eq ?_ ?_
          · exact (continuous_inner.comp
              (continuous_const.prodMk continuous_id))
          · exact (continuous_inner.comp
              (continuous_const.prodMk
                ((stinespringRepOp φ hφ (star c)).continuous)))
      | ih g =>
          rw [stinespringRepOp_coe, stinespringRepOp_coe,
            Completion.inner_coe, Completion.inner_coe]
          exact inner_stinespringActCLM_adjoint φ hφ c f g

end CStarExactness
end GroupApproximation
