import GroupApproximation.CharClass.LIXKGenChartZero
import GroupApproximation.Meta.AxiomGuard

/-!
# The chart of `S^{2n+1}` at `−e₀` as a partial homeomorphism, at rank `n`

Lane `lix-oddside-n`.  This is `CharClass/LIXSphereChart.lean` + `LIXSphereChartHomeo.lean`
with the rank a parameter and the chart at `−e₀` rather than at `−e₃`.

`sphereChartVec n` carries the domain hypothesis `chartQ n w ≤ 1`, so it is first made total by a
radial clamp, which is the identity on the closed ball.  The inverse is a formula: on the open
lower half `{Re z₀ < 0}` of the sphere, `w = (Im z₀, (z_{j+1})ⱼ)`, and the identity that closes
it is `1 − chartQ n (invFun z) = (Re z₀)²`, so the radial weight is `|Re z₀| = −Re z₀`.

## Main results

* `KGen.chartClamp`, `chartQ_clamp_le_one`, `chartClamp_eq_self`.
* `KGen.sphereLowerZero`, `KGen.sphereChartInv`, `one_sub_chartQ_inv`.
* `KGen.sphereChartHomeo n` — **the chart at `−e₀` as an `OpenPartialHomeomorph`.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The clamp -/

/-- The rescaling factor that pulls a chart point into the closed unit ball. -/
def chartScale (n : ℕ) (w : ChartBase n) : ℝ := (max 1 (Real.sqrt (chartQ n w)))⁻¹

theorem continuous_chartScale (n : ℕ) : Continuous (chartScale n) :=
  ((continuous_const.max (Real.continuous_sqrt.comp (continuous_chartQ n))).inv₀
    fun w => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _)))

/-- The clamped chart point. -/
def chartClamp (n : ℕ) (w : ChartBase n) : ChartBase n := chartScale n w • w

theorem continuous_chartClamp (n : ℕ) : Continuous (chartClamp n) :=
  (continuous_chartScale n).smul continuous_id

theorem chartQ_smul (n : ℕ) (r : ℝ) (w : ChartBase n) :
    chartQ n (r • w) = r ^ 2 * chartQ n w := by
  show (r * w.1) ^ 2 + ∑ j, ‖(r • w.2) j‖ ^ 2 = r ^ 2 * (w.1 ^ 2 + ∑ j, ‖w.2 j‖ ^ 2)
  have hs : ∀ j, ‖(r • w.2) j‖ ^ 2 = r ^ 2 * ‖w.2 j‖ ^ 2 := fun j => by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Finset.sum_congr rfl fun j _ => hs j, ← Finset.mul_sum]
  ring

/-- **The clamp lands in the closed unit ball.** -/
theorem chartQ_clamp_le_one (n : ℕ) (w : ChartBase n) : chartQ n (chartClamp n w) ≤ 1 := by
  rw [chartClamp, chartQ_smul]
  rcases le_total (chartQ n w) 1 with h | h
  · have hs : Real.sqrt (chartQ n w) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h
    rw [chartScale, max_eq_left hs, inv_one, one_pow, one_mul]
    exact h
  · have hpos : (0 : ℝ) < chartQ n w := lt_of_lt_of_le one_pos h
    have hs : (1 : ℝ) ≤ Real.sqrt (chartQ n w) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h
    have hsq : Real.sqrt (chartQ n w) ^ 2 = chartQ n w := Real.sq_sqrt hpos.le
    rw [chartScale, max_eq_right hs, inv_pow, hsq, inv_mul_cancel₀ hpos.ne']

/-- The clamp is the identity on the closed ball. -/
theorem chartClamp_eq_self {n : ℕ} {w : ChartBase n} (hw : chartQ n w ≤ 1) :
    chartClamp n w = w := by
  have hs : Real.sqrt (chartQ n w) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hw
  rw [chartClamp, chartScale, max_eq_left hs, inv_one, one_smul]

/-- **The chart at `−e₀`, total.** -/
def sphereChartFun (n : ℕ) (w : ChartBase n) : ↥(unitVectors (Fin (n + 1))) :=
  ⟨sphereChartVec n (chartClamp n w), sphereChartVec_mem (chartQ_clamp_le_one n w)⟩

theorem continuous_sphereChartFun (n : ℕ) : Continuous (sphereChartFun n) :=
  ((continuous_sphereChartVec n).comp (continuous_chartClamp n)).subtype_mk _

/-! ## 2. The open lower half and the inverse -/

/-- The part of the sphere where coordinate `0` has negative real part. -/
def sphereLowerZero (n : ℕ) : Set ↥(unitVectors (Fin (n + 1))) :=
  {z | ((z : Fin (n + 1) → ℂ) 0).re < 0}

theorem isOpen_sphereLowerZero (n : ℕ) : IsOpen (sphereLowerZero n) := by
  refine isOpen_induced_iff.mpr ⟨{v : Fin (n + 1) → ℂ | (v 0).re < 0}, ?_, rfl⟩
  exact isOpen_lt (Complex.continuous_re.comp (continuous_apply 0)) continuous_const

theorem negEZero_mem_sphereLowerZero (n : ℕ) : negEZero n ∈ sphereLowerZero n := by
  show ((((negEZero n : ↥(unitVectors (Fin (n + 1)))) : Fin (n + 1) → ℂ) 0).re) < 0
  simp [negEZero, eZero]

/-- The inverse formula. -/
def sphereChartInv (n : ℕ) (z : ↥(unitVectors (Fin (n + 1)))) : ChartBase n :=
  (((z : Fin (n + 1) → ℂ) 0).im, fun j => (z : Fin (n + 1) → ℂ) j.succ)

theorem continuous_sphereChartInv (n : ℕ) : Continuous (sphereChartInv n) := by
  refine Continuous.prodMk ?_ ?_
  · exact Complex.continuous_im.comp ((continuous_apply 0).comp continuous_subtype_val)
  · exact continuous_pi fun j => (continuous_apply j.succ).comp continuous_subtype_val

/-- **The key identity.**  On the sphere, `1 − chartQ n (invFun z) = (Re z₀)²`. -/
theorem one_sub_chartQ_inv (n : ℕ) (z : ↥(unitVectors (Fin (n + 1)))) :
    1 - chartQ n (sphereChartInv n z) = ((z : Fin (n + 1) → ℂ) 0).re ^ 2 := by
  have hz : ∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2 = 1 := mem_unitVectors_iff.mp z.2
  rw [Fin.sum_univ_succ] at hz
  have h0 : ‖(z : Fin (n + 1) → ℂ) 0‖ ^ 2
      = ((z : Fin (n + 1) → ℂ) 0).re ^ 2 + ((z : Fin (n + 1) → ℂ) 0).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  show 1 - (((z : Fin (n + 1) → ℂ) 0).im ^ 2 + ∑ j, ‖(z : Fin (n + 1) → ℂ) j.succ‖ ^ 2) = _
  linarith

/-! ## 3. The partial homeomorphism -/

/-- **The chart at `−e₀`, as a partial homeomorphism onto the open lower half.** -/
def sphereChartHomeo (n : ℕ) :
    OpenPartialHomeomorph (ChartBase n) ↥(unitVectors (Fin (n + 1))) where
  toFun := sphereChartFun n
  invFun := sphereChartInv n
  source := {w | chartQ n w < 1}
  target := sphereLowerZero n
  map_source' := by
    intro w hw
    have hw' : chartQ n w < 1 := hw
    show (sphereChartVec n (chartClamp n w) 0).re < 0
    rw [chartClamp_eq_self hw'.le]
    exact re_sphereChartVec_zero_neg hw'
  map_target' := by
    intro z hz
    show chartQ n (sphereChartInv n z) < 1
    have hkey := one_sub_chartQ_inv n z
    have hre : ((z : Fin (n + 1) → ℂ) 0).re < 0 := hz
    nlinarith [hkey, hre]
  left_inv' := by
    intro w hw
    have hw' : chartQ n w < 1 := hw
    show sphereChartInv n (sphereChartFun n w) = w
    obtain ⟨c, v⟩ := w
    simp only [sphereChartInv, sphereChartFun, chartClamp_eq_self hw'.le, sphereChartVec,
      Fin.cons_zero, Fin.cons_succ]
    simp
  right_inv' := by
    intro z hz
    have hre : ((z : Fin (n + 1) → ℂ) 0).re < 0 := hz
    have hq : chartQ n (sphereChartInv n z) < 1 := by
      have hkey := one_sub_chartQ_inv n z
      nlinarith [hkey, hre]
    refine Subtype.ext ?_
    show sphereChartVec n (chartClamp n (sphereChartInv n z)) = _
    rw [chartClamp_eq_self hq.le]
    have hw : chartWeight n (sphereChartInv n z) = -((z : Fin (n + 1) → ℂ) 0).re := by
      rw [chartWeight, one_sub_chartQ_inv, Real.sqrt_sq_eq_abs, abs_of_neg hre]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show ((sphereChartInv n z).1 : ℂ) * Complex.I - (chartWeight n (sphereChartInv n z) : ℂ)
        = (z : Fin (n + 1) → ℂ) 0
      rw [hw]
      have h1 : ((sphereChartInv n z).1 : ℂ) = (((z : Fin (n + 1) → ℂ) 0).im : ℂ) := rfl
      rw [h1]
      push_cast
      rw [sub_neg_eq_add, add_comm]
      exact Complex.re_add_im _
    · show (sphereChartInv n z).2 j = (z : Fin (n + 1) → ℂ) j.succ
      rfl
  open_source := isOpen_lt (continuous_chartQ n) continuous_const
  open_target := isOpen_sphereLowerZero n
  continuousOn_toFun := (continuous_sphereChartFun n).continuousOn
  continuousOn_invFun := (continuous_sphereChartInv n).continuousOn

theorem sphereChartHomeo_apply {n : ℕ} {w : ChartBase n} (hw : chartQ n w ≤ 1) :
    ((sphereChartHomeo n w : ↥(unitVectors (Fin (n + 1)))) : Fin (n + 1) → ℂ)
      = sphereChartVec n w := by
  show sphereChartVec n (chartClamp n w) = _
  rw [chartClamp_eq_self hw]

theorem zero_mem_sphereChartHomeo_source (n : ℕ) : (0 : ChartBase n) ∈ (sphereChartHomeo n).source := by
  show chartQ n 0 < 1
  simp [chartQ]

theorem sphereChartHomeo_zero (n : ℕ) : sphereChartHomeo n 0 = negEZero n := by
  refine Subtype.ext ?_
  rw [sphereChartHomeo_apply (by simp [chartQ]), sphereChartVec_zero]
  rfl

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.chartQ_clamp_le_one
#audit_axioms KGen.one_sub_chartQ_inv
#audit_axioms KGen.sphereChartHomeo_zero

end GroupApproximation.CharClass
