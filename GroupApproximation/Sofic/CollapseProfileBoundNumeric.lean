import GroupApproximation.Sofic.CollapseProfileBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical form of the collapse profile bound

Continued from `Sofic/CollapseProfileBound.lean`, whose header records that the
Step-5 sentence both modules formalize was deleted from
`non_mf_groups_exist.tex` in commit `3a45fa60`.

`CollapseProfileBound.collapse_profile_le` bounds the limiting profile of
the collapse family by `160 * Real.log 2 / κ ^ 2`.  This module records
the two numerical consequences, which are the only ones needing
`Real.log_two_lt_d9`:

* `collapse_profile_le_num` — the profile is at most `111 / κ ^ 2`;
* `collapse_cw_le` — the endpoint constant `Cw = √R + 2` of
  `InvolutionCollapseEndpoint.no_marked_model` is at most `11 / κ + 2`.

The second is what makes every later constant of the endpoint
(`ρt`, `θ`, `τ`, `q`, `d₀`, `ε₆`) an explicit function of `κ` and `|S|`
alone.  This file is separated from `CollapseProfileBound.lean` so that
the `Mathlib.Analysis.Complex.ExponentialBounds` import stays local to
the numerics.
-/

namespace GroupApproximation
namespace CollapseProfileBound

/-! ## Two arithmetic facts about `160 * log 2` -/

/-- `160 * log 2 ≈ 110.90 < 111`. -/
theorem mul_log_two_le_num : 160 * Real.log 2 ≤ 111 := by
  linarith [Real.log_two_lt_d9]

/-- `√(160 * log 2) ≈ 10.53 < 11`, in the scaled form the endpoint
needs. -/
theorem sqrt_bound_le {κ : ℝ} (hκ : 0 < κ) :
    Real.sqrt (160 * Real.log 2 / κ ^ 2) ≤ 11 / κ := by
  have hκ2 : (0 : ℝ) < κ ^ 2 := pow_pos hκ 2
  have h121 : 160 * Real.log 2 ≤ 121 := by
    linarith [Real.log_two_lt_d9]
  have hle : 160 * Real.log 2 / κ ^ 2 ≤ (11 / κ) ^ 2 := by
    have hsq : (11 / κ) ^ 2 = 121 / κ ^ 2 := by
      rw [div_pow]
      norm_num
    rw [hsq]
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h121 (inv_nonneg.mpr hκ2.le)
  have hmono := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 11 / κ)] at hmono

/-- **The endpoint constant, explicitly.**  With the profile bound
`R = 160 * log 2 / κ ^ 2` of `collapse_profile_le`, the constant
`Cw = √R + 2` used by `InvolutionCollapseEndpoint.no_marked_model` is at
most `11 / κ + 2`. -/
theorem collapse_cw_le {κ : ℝ} (hκ : 0 < κ) :
    Real.sqrt (160 * Real.log 2 / κ ^ 2) + 2 ≤ 11 / κ + 2 := by
  linarith [sqrt_bound_le hκ]

/-! ## The numerical profile bound for the collapse family -/

section Collapse

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open Ultralimit UltralimitGaussian KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-- **The collapse profile bound, numerically.**  The limiting profile of
the normalized displacement family is at most `111 / κ ^ 2`, where `κ` is
the Kazhdan constant of the pair `(S, κ)` — no other data of the
situation enters. -/
theorem collapse_profile_le_num_of_data
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {κ : ℝ} (hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ) :
    seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ 111 / κ ^ 2 := by
  have hκ : (0 : ℝ) < κ := hpair.1
  have hκ2 : (0 : ℝ) < κ ^ 2 := pow_pos hκ 2
  refine le_trans (collapse_profile_le B iota k V S hgen hsymm hVinv
    hVcomm hVconv hmark hpair γ) ?_
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right mul_log_two_le_num
    (inv_nonneg.mpr hκ2.le)

/-- **The numerical collapse profile bound, with every input bound after the
colon.**  The declaration the manuscript badges at `eq:profile-explicit` for
its second inequality, `111/κ²`.  As with `collapse_profile_le`, the leading
binders are moved after the colon because a badge on a declaration with
declaration inputs certifies a parameterized statement rather than the printed
one; the mathematics is `collapse_profile_le_num_of_data`. -/
theorem collapse_profile_le_num :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
      (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
      (_hgen : Subgroup.closure (S : Set Γ) = ⊤)
      (_hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
      (_hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
      (_hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
      (_hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
      (_hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
      {κ : ℝ} (_hpair : IsKazhdanPair.{0, 0} Γ S κ) (γ : Γ),
      seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ 111 / κ ^ 2 := by
  intro Γ E _ _ B iota k V S hgen hsymm hVinv hVcomm hVconv hmark κ hpair γ
  exact collapse_profile_le_num_of_data B iota k V S hgen hsymm hVinv hVcomm
    hVconv hmark hpair γ

end Collapse

end CollapseProfileBound
end GroupApproximation
