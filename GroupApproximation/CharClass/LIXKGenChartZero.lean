import GroupApproximation.CharClass.LIXKGenSector
import GroupApproximation.CharClass.LIXKGenChart
import GroupApproximation.Meta.AxiomGuard

/-!
# The chart of `S^{2n+1}` at the `j`-th zero, in which `Ψ_k` is the chart at `−e₀`

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3a, test K6).

The chart at the `j`-th zero `kZeroVec n k j = ζ_j e₀` is the chart at `−e₀` post-composed, in
coordinate `0`, with the branch `κ_j` of `CharClass/LIXKGenSect.lean`:

```text
chartZeroVec n k j w := Function.update (sphereChartVec n w) 0 (κ_j (sphereChartVec n w 0)) .
```

Because `joinC k ∘ κ_j = id` holds everywhere, `psiVec n k ∘ chartZeroVec n k j = sphereChartVec n`
on the whole chart source, with no hypothesis.  So the trivial block of the `k`-section,
`(1−τ) e₀ + τ · Ψ_k(x)`, read in the chart at the `j`-th zero, is `trivialBlockChart n` at EVERY
`j`: one local model serves all `k+1` zeros, and neither `Ψ_k` nor `κ_j` is ever differentiated.

Model test K6 of the predecessor (`Ψ_k ∘ chart_j = sphereChart` on the sphere, `n ∈ {2,3,4}`,
`k ≤ 5`, worst `6.8e−15`) and S1 of `nm/lixoddn/ksect_modeltest.py` cover the identities.

## Main results

* `KGen.chartZeroVec`, `chartZeroVec_zero` (centred at the `j`-th zero), `chartZeroVec_mem`.
* `KGen.psiVec_chartZeroVec` — **`Ψ_k ∘ chart_j = chart at −e₀`.**
* `KGen.trivialBlockK_chartZeroVec` — the section's trivial block in the chart at the `j`-th zero
  is `trivialBlockChart n`.
* `KGen.continuousOn_chartZeroVec` — continuity on the open chart source.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.STW59
open GroupApproximation.LIX.Powers

/-- **The chart vector at the `j`-th zero.** -/
def chartZeroVec (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n) : Fin (n + 1) → ℂ :=
  Function.update (sphereChartVec n w) 0 (kSect k j (sphereChartVec n w 0))

@[simp] theorem chartZeroVec_apply_zero (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n) :
    chartZeroVec n k j w 0 = kSect k j (sphereChartVec n w 0) :=
  Function.update_self _ _ _

theorem chartZeroVec_apply_of_ne (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n)
    {i : Fin (n + 1)} (hi : i ≠ 0) : chartZeroVec n k j w i = sphereChartVec n w i :=
  Function.update_of_ne hi _ _

/-- **`Ψ_k ∘ chart_j = chart at −e₀`**, on the whole chart source. -/
theorem psiVec_chartZeroVec (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n) :
    psiVec n k (chartZeroVec n k j w) = sphereChartVec n w := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, chartZeroVec_apply_zero, joinC_kSect]
  · rw [psiVec_apply_of_ne n k _ hi, chartZeroVec_apply_of_ne n k j w hi]

/-- The chart at the `j`-th zero is centred there. -/
theorem chartZeroVec_zero (n k : ℕ) (j : Fin (k + 1)) :
    chartZeroVec n k j 0 = kZeroVec n k j := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [chartZeroVec_apply_zero, kZeroVec_apply_zero, sphereChartVec_zero, Pi.neg_apply,
      eZero_apply_zero, kSect_neg_one]
  · rw [chartZeroVec_apply_of_ne n k j 0 hi, kZeroVec_apply_of_ne n k j hi,
      sphereChartVec_zero, Pi.neg_apply, eZero_apply_of_ne n hi, neg_zero]

theorem norm_chartZeroVec_apply (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n)
    (i : Fin (n + 1)) : ‖chartZeroVec n k j w i‖ = ‖sphereChartVec n w i‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [chartZeroVec_apply_zero, norm_kSect]
  · rw [chartZeroVec_apply_of_ne n k j w hi]

/-- The chart at the `j`-th zero lands on the unit sphere. -/
theorem chartZeroVec_mem {n k : ℕ} {j : Fin (k + 1)} {w : ChartBase n} (hw : chartQ n w ≤ 1) :
    chartZeroVec n k j w ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff]
  have h := mem_unitVectors_iff.mp (sphereChartVec_mem (n := n) hw)
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by rw [norm_chartZeroVec_apply]

/-- **The trivial block of the `k`-section in the chart at the `j`-th zero is the one-zero
trivial block at `−e₀`.** -/
theorem trivialBlockK_chartZeroVec (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n) (u : ℝ) :
    (fun i => ((1 - (1 + u) / 2 : ℝ) : ℂ) * eZero n i
        + (((1 + u) / 2 : ℝ) : ℂ) * psiVec n k (chartZeroVec n k j w) i)
      = trivialBlockChart n w u := by
  show _ = fun i => ((1 - (1 + u) / 2 : ℝ) : ℂ) * eZero n i
    + (((1 + u) / 2 : ℝ) : ℂ) * sphereChartVec n w i
  rw [psiVec_chartZeroVec]

/-- On the open chart source the zeroth coordinate of the chart at `−e₀` has negative real
part. -/
theorem re_sphereChartVec_zero_neg {n : ℕ} {w : ChartBase n} (hw : chartQ n w < 1) :
    (sphereChartVec n w 0).re < 0 := by
  have hpos : 0 < chartWeight n w := Real.sqrt_pos.mpr (by linarith)
  simp only [sphereChartVec, Fin.cons_zero, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, zero_sub]
  linarith

theorem neg_sphereChartVec_zero_mem_slitPlane {n : ℕ} {w : ChartBase n} (hw : chartQ n w < 1) :
    -sphereChartVec n w 0 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [Complex.neg_re]
  linarith [re_sphereChartVec_zero_neg hw]

/-- The chart at the `j`-th zero maps the open chart source into the sector around `ζ_j`. -/
theorem chartZeroVec_zero_mem_kSector {n k : ℕ} (j : Fin (k + 1)) {w : ChartBase n}
    (hw : chartQ n w < 1) : chartZeroVec n k j w 0 ∈ kSector k j := by
  rw [chartZeroVec_apply_zero]
  exact kSect_mem_kSector k j (neg_sphereChartVec_zero_mem_slitPlane hw)

/-- **The chart at the `j`-th zero is continuous on the open chart source.** -/
theorem continuousOn_chartZeroVec (n k : ℕ) (j : Fin (k + 1)) :
    ContinuousOn (chartZeroVec n k j) {w : ChartBase n | chartQ n w < 1} := by
  intro w hw
  refine continuousAt_pi.mpr (fun i => ?_) |>.continuousWithinAt
  rcases eq_or_ne i 0 with rfl | hi
  · have h0 : ContinuousAt (fun v : ChartBase n => sphereChartVec n v 0) w :=
      ((continuous_apply 0).comp (continuous_sphereChartVec n)).continuousAt
    have hk := (continuousAt_kSect k j (neg_sphereChartVec_zero_mem_slitPlane hw)).comp h0
    simpa only [chartZeroVec_apply_zero] using hk
  · have h := ((continuous_apply i).comp (continuous_sphereChartVec n)).continuousAt (x := w)
    simpa only [chartZeroVec_apply_of_ne n k j _ hi] using h

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.psiVec_chartZeroVec
#audit_axioms KGen.chartZeroVec_zero
#audit_axioms KGen.chartZeroVec_mem
#audit_axioms KGen.continuousOn_chartZeroVec

end GroupApproximation.CharClass
