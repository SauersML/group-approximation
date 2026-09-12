import GroupApproximation.CharClass.LIXSectionChart

/-!
# The five-sphere factor of the base chart

Lane `cc-lix-odd`, the second of the base chart's three factors.

`LIXSectionChart` has `sphereChartVec` and `sphereChart`, but the latter carries the
domain hypothesis `‖w₁‖² + ‖w₂‖² + w₃² ≤ 1` as an argument, so it is not a map on the
plain product and cannot be an `OpenPartialHomeomorph` as it stands.

This file makes it total by a **radial clamp**, the same device as the circle factor: the
coordinate is rescaled into the closed unit ball, which is the identity on the open ball,
so continuity is a composition and the ball is used only to identify the clamp with the
identity on the source.

## Main results

* `sphereQ`, `sphereClamp` — the radial quantity and the clamp, with `sphereQ_clamp_le_one`.
* `sphereChartFun` — the chart map, total and continuous.
* `sphereChartFun_zero` — the origin goes to `-e₃`, which is the section's zero.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The radial quantity and the clamp -/

/-- The squared radius of a chart coordinate. -/
def sphereQ (w : ℂ × ℂ × ℝ) : ℝ := ‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2

theorem sphereQ_nonneg (w : ℂ × ℂ × ℝ) : 0 ≤ sphereQ w := by
  have h1 : (0:ℝ) ≤ ‖w.1‖ ^ 2 := by positivity
  have h2 : (0:ℝ) ≤ ‖w.2.1‖ ^ 2 := by positivity
  have h3 : (0:ℝ) ≤ w.2.2 ^ 2 := by positivity
  unfold sphereQ; linarith

theorem continuous_sphereQ : Continuous sphereQ := by
  unfold sphereQ; fun_prop

/-- The rescaling factor that pulls a coordinate into the closed unit ball. -/
def sphereScale (w : ℂ × ℂ × ℝ) : ℝ := (max 1 (Real.sqrt (sphereQ w)))⁻¹

theorem sphereScale_pos (w : ℂ × ℂ × ℝ) : 0 < sphereScale w := by
  have h : (0:ℝ) < max 1 (Real.sqrt (sphereQ w)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  exact inv_pos.mpr h

theorem continuous_sphereScale : Continuous sphereScale := by
  unfold sphereScale
  exact ((continuous_const.max (Real.continuous_sqrt.comp continuous_sphereQ)).inv₀
    fun w => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _)))

/-- The clamped coordinate. -/
def sphereClamp (w : ℂ × ℂ × ℝ) : ℂ × ℂ × ℝ := sphereScale w • w

theorem continuous_sphereClamp : Continuous sphereClamp := by
  unfold sphereClamp
  exact continuous_sphereScale.smul continuous_id

theorem sphereQ_smul (r : ℝ) (w : ℂ × ℂ × ℝ) : sphereQ (r • w) = r ^ 2 * sphereQ w := by
  show ‖r • w.1‖ ^ 2 + ‖r • w.2.1‖ ^ 2 + (r * w.2.2) ^ 2 = _
  rw [norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  unfold sphereQ
  ring

/-- **The clamp lands in the closed unit ball.** -/
theorem sphereQ_clamp_le_one (w : ℂ × ℂ × ℝ) : sphereQ (sphereClamp w) ≤ 1 := by
  rw [sphereClamp, sphereQ_smul]
  rcases le_total (sphereQ w) 1 with h | h
  · have hs : Real.sqrt (sphereQ w) ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h
    have : sphereScale w = 1 := by
      rw [sphereScale, max_eq_left hs, inv_one]
    rw [this]
    simpa using h
  · have hpos : (0:ℝ) < sphereQ w := lt_of_lt_of_le one_pos h
    have hs : (1:ℝ) ≤ Real.sqrt (sphereQ w) := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h
    have hmax : max 1 (Real.sqrt (sphereQ w)) = Real.sqrt (sphereQ w) := max_eq_right hs
    have hsq : Real.sqrt (sphereQ w) ^ 2 = sphereQ w := Real.sq_sqrt (le_of_lt hpos)
    have hne : Real.sqrt (sphereQ w) ≠ 0 := by positivity
    rw [sphereScale, hmax, inv_pow, hsq]
    rw [inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The clamp is the identity inside the closed ball. -/
theorem sphereClamp_eq_self {w : ℂ × ℂ × ℝ} (hw : sphereQ w ≤ 1) : sphereClamp w = w := by
  have hs : Real.sqrt (sphereQ w) ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hw
  have : sphereScale w = 1 := by rw [sphereScale, max_eq_left hs, inv_one]
  rw [sphereClamp, this, one_smul]

/-! ## 2. The chart map -/

/-- **The five-sphere chart, total.** -/
def sphereChartFun (w : ℂ × ℂ × ℝ) : ↥(unitVectors (Fin 3)) :=
  ⟨sphereChartVec (sphereClamp w), sphereChartVec_mem (sphereQ_clamp_le_one w)⟩

theorem continuous_sphereChartFun : Continuous sphereChartFun :=
  ((continuous_sphereChartVec).comp continuous_sphereClamp).subtype_mk _

/-- The origin of the chart is the section's zero on this factor. -/
theorem sphereChartFun_zero : sphereChartFun 0 = negEThree := by
  refine Subtype.ext ?_
  show sphereChartVec (sphereClamp 0) = _
  rw [sphereClamp_eq_self (by simp [sphereQ])]
  simp [negEThree]

end GroupApproximation.CharClass
