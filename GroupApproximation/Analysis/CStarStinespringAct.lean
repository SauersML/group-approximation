import GroupApproximation.Analysis.CStarStinespringSpace
import GroupApproximation.Analysis.CStarStinespringBound

/-!
# The multiplication action on the dilation pre-space

## What this module proves

The Stinespring representation acts on the free model `A →₀ H` by
multiplication on the index: `single a x ↦ single (c * a) x`.  This
module constructs that action and proves the inequality that makes it
bounded for the dilation seminorm:

  `⟨π(c) f, π(c) f⟩ ≤ ‖c‖² ⟨f, f⟩`  (real parts),

whenever the defect `‖c‖² • 1 - star c * c` is exhibited as
`star d * d`.  The proof is the classical one: expand
`star a * (star d * d) * b` by the defect identity, recognize the two
resulting double sums as `‖c‖² ⟨f, f⟩` and `⟨π(c) f, π(c) f⟩`, and
apply the weighted form positivity of `CStarStinespringBound` to the
support of `f`.  The seminorm form on `StinespringPre` follows by
monotonicity of the square root.

The exhibition of the defect as `star d * d` -- order theory in `A` --
and the extension of the action to the completion are later modules.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finsupp

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {φ : A →ₗ[ℂ] (H →L[ℂ] H)}

/-! ## The action on the free model -/

/-- Multiplication by `c` on the index of the free model: the map
`∑ a ⊗ x_a ↦ ∑ (c * a) ⊗ x_a`. -/
noncomputable def stinespringActFree (c : A) :
    (A →₀ H) →ₗ[ℂ] (A →₀ H) :=
  Finsupp.lmapDomain H ℂ (fun a => c * a)

@[simp] theorem stinespringActFree_single (c a : A) (x : H) :
    stinespringActFree c (Finsupp.single a x)
      = Finsupp.single (c * a) x := by
  rw [stinespringActFree, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ## The form under the action -/

theorem stinespringSesq_act_left (c : A) (f g : A →₀ H) :
    stinespringSesq φ (stinespringActFree c f) g
      = f.sum fun a x => g.sum fun b y =>
          ⟪x, φ (star (c * a) * b) y⟫_ℂ := by
  classical
  rw [stinespringActFree, Finsupp.lmapDomain_apply]
  unfold stinespringSesq
  exact Finsupp.sum_mapDomain_index (fun a' => by simp)
    (fun a' x₁ x₂ => by simp [Finsupp.sum_add])

theorem stinespringSesq_act_act (c : A) (f : A →₀ H) :
    stinespringSesq φ (stinespringActFree c f) (stinespringActFree c f)
      = f.sum fun a x => f.sum fun b y =>
          ⟪x, φ (star (c * a) * (c * b)) y⟫_ℂ := by
  classical
  rw [stinespringSesq_act_left]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [stinespringActFree, Finsupp.lmapDomain_apply]
  exact Finsupp.sum_mapDomain_index (fun b' => by simp)
    (fun b' y₁ y₂ => by simp)

section WithComplete

variable [CompleteSpace H]

/-- **The dilation bound at the form level**: whenever the defect
`‖c‖² • 1 - star c * c` is exhibited as `star d * d`, the form of the
translated family is dominated by `‖c‖²` times the form. -/
theorem re_stinespringSesq_act_le (hφ : IsCompletelyPositive φ)
    (c d : A)
    (hd : star d * d = ((‖c‖ ^ 2 : ℝ) : ℂ) • (1 : A) - star c * c)
    (f : A →₀ H) :
    (stinespringSesq φ (stinespringActFree c f)
        (stinespringActFree c f)).re
      ≤ ‖c‖ ^ 2 * (stinespringSesq φ f f).re := by
  classical
  have halg : ∀ a b : A, star a * (star d * d) * b
      = ((‖c‖ ^ 2 : ℝ) : ℂ) • (star a * b)
        - star (c * a) * (c * b) := by
    intro a b
    rw [hd]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      star_mul, mul_assoc]
  have hE : 0 ≤ (f.sum fun a x => f.sum fun b y =>
      ⟪x, φ (star a * (star d * d) * b) y⟫_ℂ).re :=
    (hφ.form_nonneg_middle_finset f.support d fun a => f a).1
  have hsplit : (f.sum fun a x => f.sum fun b y =>
        ⟪x, φ (star a * (star d * d) * b) y⟫_ℂ)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * stinespringSesq φ f f
        - stinespringSesq φ (stinespringActFree c f)
            (stinespringActFree c f) := by
    rw [stinespringSesq_act_act]
    unfold stinespringSesq
    show (∑ a ∈ f.support, ∑ b ∈ f.support,
        ⟪f a, φ (star a * (star d * d) * b) (f b)⟫_ℂ)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * (∑ a ∈ f.support, ∑ b ∈ f.support,
          ⟪f a, φ (star a * b) (f b)⟫_ℂ)
        - ∑ a ∈ f.support, ∑ b ∈ f.support,
            ⟪f a, φ (star (c * a) * (c * b)) (f b)⟫_ℂ
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [halg a b, map_sub, map_smul, _root_.sub_apply,
      _root_.smul_apply, inner_sub_right, inner_smul_right]
  rw [hsplit] at hE
  have hre : (((‖c‖ ^ 2 : ℝ) : ℂ) * stinespringSesq φ f f
      - stinespringSesq φ (stinespringActFree c f)
          (stinespringActFree c f)).re
      = ‖c‖ ^ 2 * (stinespringSesq φ f f).re
        - (stinespringSesq φ (stinespringActFree c f)
            (stinespringActFree c f)).re := by
    rw [Complex.sub_re, Complex.re_ofReal_mul]
  rw [hre] at hE
  linarith

/-! ## The action on the pre-space, with its seminorm bound -/

variable (φ) (hφ : IsCompletelyPositive φ) in
/-- The multiplication action, transported to the pre-space. -/
noncomputable def stinespringActPre (c : A) :
    StinespringPre φ hφ →ₗ[ℂ] StinespringPre φ hφ :=
  ((toStinespringPre φ hφ).toLinearMap.comp
    (stinespringActFree c)).comp (ofStinespringPre φ hφ).toLinearMap

variable (φ) (hφ : IsCompletelyPositive φ)

@[simp] theorem stinespringActPre_apply (c : A) (f : StinespringPre φ hφ) :
    stinespringActPre φ hφ c f
      = toStinespringPre φ hφ
          (stinespringActFree c (ofStinespringPre φ hφ f)) := rfl

@[simp] theorem stinespringPre_norm_def (f : StinespringPre φ hφ) :
    ‖f‖ = Real.sqrt (stinespringSesq φ (ofStinespringPre φ hφ f)
      (ofStinespringPre φ hφ f)).re := rfl

/-- **The dilation bound at the seminorm level.** -/
theorem norm_stinespringActPre_le (c d : A)
    (hd : star d * d = ((‖c‖ ^ 2 : ℝ) : ℂ) • (1 : A) - star c * c)
    (f : StinespringPre φ hφ) :
    ‖stinespringActPre φ hφ c f‖ ≤ ‖c‖ * ‖f‖ := by
  rw [stinespringPre_norm_def, stinespringPre_norm_def]
  have h1 : (stinespringSesq φ
      (ofStinespringPre φ hφ (stinespringActPre φ hφ c f))
      (ofStinespringPre φ hφ (stinespringActPre φ hφ c f))).re
      ≤ ‖c‖ ^ 2 * (stinespringSesq φ (ofStinespringPre φ hφ f)
          (ofStinespringPre φ hφ f)).re :=
    re_stinespringSesq_act_le hφ c d hd (ofStinespringPre φ hφ f)
  calc Real.sqrt (stinespringSesq φ
        (ofStinespringPre φ hφ (stinespringActPre φ hφ c f))
        (ofStinespringPre φ hφ (stinespringActPre φ hφ c f))).re
      ≤ Real.sqrt (‖c‖ ^ 2 * (stinespringSesq φ
          (ofStinespringPre φ hφ f) (ofStinespringPre φ hφ f)).re) :=
        Real.sqrt_le_sqrt h1
    _ = ‖c‖ * Real.sqrt (stinespringSesq φ
          (ofStinespringPre φ hφ f) (ofStinespringPre φ hφ f)).re := by
        rw [Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]

end WithComplete

end CStarExactness
end GroupApproximation
