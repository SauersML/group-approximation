import GroupApproximation.Analysis.CStarStinespringRep

/-!
# Linearity of the dilation representation

## What this module proves

On the free model, `π(c₁ + c₂) f` and `π(c₁) f + π(c₂) f` are different
finitely supported families -- translation of indices is not additive
in the translating element.  Their difference is nevertheless a **null
vector** of the Stinespring form: the form is linear in the element
through the argument of `φ`, so pairing the difference against anything
gives `φ(0) = 0`.  Null vectors vanish in the completion, so the
extended operators are additive there; the same argument gives
homogeneity.

* `stinespringSesq_act_add_left`, `stinespringSesq_act_smul_left` --
  linearity of the form in the acting element;
* `stinespringRepOp_add`, `stinespringRepOp_smul` -- the operator laws
  on the Stinespring space.

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

/-! ## Linearity of the form in the acting element -/

theorem stinespringSesq_sub_left {φ : A →ₗ[ℂ] (H →L[ℂ] H)}
    (u v g : A →₀ H) :
    stinespringSesq φ (u - v) g
      = stinespringSesq φ u g - stinespringSesq φ v g := by
  have h := stinespringSesq_add_left φ (u - v) v g
  rw [sub_add_cancel] at h
  rw [h]
  ring

theorem stinespringSesq_act_add_left {φ : A →ₗ[ℂ] (H →L[ℂ] H)}
    (c₁ c₂ : A) (f g : A →₀ H) :
    stinespringSesq φ (stinespringActFree (c₁ + c₂) f) g
      = stinespringSesq φ (stinespringActFree c₁ f) g
        + stinespringSesq φ (stinespringActFree c₂ f) g := by
  classical
  rw [stinespringSesq_act_left, stinespringSesq_act_left,
    stinespringSesq_act_left, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun b _ => ?_
  have h : star ((c₁ + c₂) * a) * b
      = star (c₁ * a) * b + star (c₂ * a) * b := by
    rw [add_mul, star_add, add_mul]
  rw [h, map_add, add_apply, inner_add_right]

theorem stinespringSesq_act_smul_left {φ : A →ₗ[ℂ] (H →L[ℂ] H)}
    (r : ℂ) (c : A) (f g : A →₀ H) :
    stinespringSesq φ (stinespringActFree (r • c) f) g
      = (starRingEnd ℂ) r
        * stinespringSesq φ (stinespringActFree c f) g := by
  classical
  rw [stinespringSesq_act_left, stinespringSesq_act_left]
  show (∑ a ∈ f.support, ∑ b ∈ g.support,
      ⟪f a, φ (star ((r • c) * a) * b) (g b)⟫_ℂ)
    = (starRingEnd ℂ) r * ∑ a ∈ f.support, ∑ b ∈ g.support,
        ⟪f a, φ (star (c * a) * b) (g b)⟫_ℂ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : star ((r • c) * a) * b
      = (starRingEnd ℂ) r • (star (c * a) * b) := by
    rw [smul_mul_assoc, star_smul, smul_mul_assoc]
    rfl
  rw [h, map_smul, ContinuousLinearMap.smul_apply, inner_smul_right]

section WithComplete

variable [CompleteSpace H]
variable (φ : A →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositive φ)

/-! ## The null differences -/

theorem norm_actPre_add_defect (c₁ c₂ : A) (f : StinespringPre φ hφ) :
    ‖stinespringActPre φ hφ (c₁ + c₂) f
      - (stinespringActPre φ hφ c₁ f + stinespringActPre φ hφ c₂ f)‖
      = 0 := by
  rw [stinespringPre_norm_def]
  have hw : stinespringSesq φ
      (stinespringActFree (c₁ + c₂) (ofStinespringPre φ hφ f)
        - (stinespringActFree c₁ (ofStinespringPre φ hφ f)
          + stinespringActFree c₂ (ofStinespringPre φ hφ f)))
      (stinespringActFree (c₁ + c₂) (ofStinespringPre φ hφ f)
        - (stinespringActFree c₁ (ofStinespringPre φ hφ f)
          + stinespringActFree c₂ (ofStinespringPre φ hφ f))) = 0 := by
    set u := stinespringActFree (c₁ + c₂) (ofStinespringPre φ hφ f)
    set v := stinespringActFree c₁ (ofStinespringPre φ hφ f)
      + stinespringActFree c₂ (ofStinespringPre φ hφ f)
    have hleft : ∀ g : A →₀ H,
        stinespringSesq φ (u - v) g = 0 := by
      intro g
      rw [stinespringSesq_sub_left, stinespringSesq_add_left,
        stinespringSesq_act_add_left]
      ring
    exact hleft (u - v)
  have hzero : (stinespringSesq φ
      (ofStinespringPre φ hφ (stinespringActPre φ hφ (c₁ + c₂) f
        - (stinespringActPre φ hφ c₁ f + stinespringActPre φ hφ c₂ f)))
      (ofStinespringPre φ hφ (stinespringActPre φ hφ (c₁ + c₂) f
        - (stinespringActPre φ hφ c₁ f
          + stinespringActPre φ hφ c₂ f)))) = 0 := hw
  rw [hzero]
  simp

theorem norm_actPre_smul_defect (r : ℂ) (c : A)
    (f : StinespringPre φ hφ) :
    ‖stinespringActPre φ hφ (r • c) f
      - r • stinespringActPre φ hφ c f‖ = 0 := by
  rw [stinespringPre_norm_def]
  have hw : stinespringSesq φ
      (stinespringActFree (r • c) (ofStinespringPre φ hφ f)
        - r • stinespringActFree c (ofStinespringPre φ hφ f))
      (stinespringActFree (r • c) (ofStinespringPre φ hφ f)
        - r • stinespringActFree c (ofStinespringPre φ hφ f)) = 0 := by
    set u := stinespringActFree (r • c) (ofStinespringPre φ hφ f)
    set v := r • stinespringActFree c (ofStinespringPre φ hφ f)
    have hleft : ∀ g : A →₀ H, stinespringSesq φ (u - v) g = 0 := by
      intro g
      rw [stinespringSesq_sub_left, stinespringSesq_smul_left,
        stinespringSesq_act_smul_left]
      ring
    exact hleft (u - v)
  have hzero : (stinespringSesq φ
      (ofStinespringPre φ hφ (stinespringActPre φ hφ (r • c) f
        - r • stinespringActPre φ hφ c f))
      (ofStinespringPre φ hφ (stinespringActPre φ hφ (r • c) f
        - r • stinespringActPre φ hφ c f))) = 0 := hw
  rw [hzero]
  simp

/-! ## The operator laws on the completion -/

theorem stinespringRepOp_add (c₁ c₂ : A) :
    stinespringRepOp φ hφ (c₁ + c₂)
      = stinespringRepOp φ hφ c₁ + stinespringRepOp φ hφ c₂ := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (stinespringRepOp φ hφ (c₁ + c₂)).continuous
        (stinespringRepOp φ hφ c₁ + stinespringRepOp φ hφ c₂).continuous
  | ih f =>
      rw [add_apply, stinespringRepOp_coe, stinespringRepOp_coe,
        stinespringRepOp_coe, ← Completion.coe_add]
      refine dist_eq_zero.mp ?_
      rw [Completion.dist_eq, dist_eq_norm]
      exact norm_actPre_add_defect φ hφ c₁ c₂ f

theorem stinespringRepOp_smul (r : ℂ) (c : A) :
    stinespringRepOp φ hφ (r • c) = r • stinespringRepOp φ hφ c := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (stinespringRepOp φ hφ (r • c)).continuous
        (r • stinespringRepOp φ hφ c).continuous
  | ih f =>
      rw [ContinuousLinearMap.smul_apply, stinespringRepOp_coe,
        stinespringRepOp_coe, ← Completion.coe_smul]
      refine dist_eq_zero.mp ?_
      rw [Completion.dist_eq, dist_eq_norm]
      exact norm_actPre_smul_defect φ hφ r c f

end WithComplete

end CStarExactness
end GroupApproximation
