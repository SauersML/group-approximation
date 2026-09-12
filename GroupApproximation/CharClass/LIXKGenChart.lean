import GroupApproximation.CharClass.LIXKGenMap
import GroupApproximation.CharClass.LIXSectionPath
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import GroupApproximation.Meta.AxiomGuard

/-!
# The chart of `S^{2n+1}` at `−e₀`, and the linear model of the section there, at rank `n`

Lane `lix-oddside-n` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4; predecessor report
`notes/lix-stronger-lane-reports/sp-oddside-n.md` §0.3, file E).

`CharClass/LIXSectionChart.lean` charts `S⁵` at `−e₃` on `ℂ × ℂ × ℝ`.  The `k`-zero geometry
moves the constant section to `e₀` (the antipode of `e_last` is a suspension point, where a
hemisphere-preserving map is a cone and not a local homeomorphism), so the chart here is at
`−e₀` and the source is `ℝ × (Fin n → ℂ)`: the imaginary part of coordinate `0`, plus the other
`n` coordinates entire,

```text
sphereChartVec n (c, v) = Fin.cons (c·i − √(1 − (c² + ∑ⱼ ‖vⱼ‖²))) v .
```

With the circle coordinate the source is `(ℝ × (Fin n → ℂ)) × ℝ`, `2n + 2` real dimensions,
matching `ℂ^{n+1}`.  The derivative of the trivial block `(1−τ) e₀ + τ x` at the zero is

```text
(dc, dv, du) ↦ Fin.cons (dc·i/2 − du) (dv/2) ,
```

`eulerLinearModel n`, a linear isomorphism by an explicit inverse
`z ↦ ((2·Im z₀, 2·z_{j+1}), −Re z₀)`.

Model-tested (`nm/lixoddn/chart_n_modeltest.py`, MSI acn112, `n ≤ 5`, 30 checks, 0 failures):
the chart is centred at `−e₀` and lands on the sphere, the Jacobian of the trivial block at the
origin is `eulerLinearModel n` (central differences in all `2n+2` directions, error `< 1e−6`),
the inverse is the stated one, and the block vanishes only at the origin near it.

## Main results

* `KGen.sphereChartVec`, `sphereChartVec_zero`, `sphereChartVec_mem` — the chart.
* `KGen.eulerLinearModel`, `eulerContinuousLinearEquiv` — the derivative, as a continuous
  linear equivalence.
* `KGen.trivialBlockChart_eq_zero_iff`, `trivialBlockChart_zero` — the zero in the chart is the
  origin.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.STW59

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. The chart of `S^{2n+1}` at `−e₀` -/

/-- The sphere half of the chart source: the imaginary part of coordinate `0` and the other
`n` coordinates. -/
abbrev ChartBase (n : ℕ) : Type := ℝ × (Fin n → ℂ)

/-- The source of the chart of `S^{2n+1} × S¹` at the zero. -/
abbrev ChartSrc (n : ℕ) : Type := ChartBase n × ℝ

/-- The squared radius of a chart point. -/
def chartQ (n : ℕ) (w : ChartBase n) : ℝ := w.1 ^ 2 + ∑ j, ‖w.2 j‖ ^ 2

theorem chartQ_nonneg (n : ℕ) (w : ChartBase n) : 0 ≤ chartQ n w :=
  add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The radial weight of the chart: `√(1 − ‖w‖²)`. -/
def chartWeight (n : ℕ) (w : ChartBase n) : ℝ := Real.sqrt (1 - chartQ n w)

/-- **The chart of `S^{2n+1}` at `−e₀`.** -/
def sphereChartVec (n : ℕ) (w : ChartBase n) : Fin (n + 1) → ℂ :=
  Fin.cons ((w.1 : ℂ) * Complex.I - (chartWeight n w : ℂ)) w.2

theorem sphereChartVec_zero (n : ℕ) : sphereChartVec n 0 = -eZero n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sphereChartVec, chartWeight, chartQ, eZero]
  · simp [sphereChartVec, eZero]

/-- The squared norm of a `Fin.cons`. -/
theorem normSq_cons (n : ℕ) (x : ℂ) (v : Fin n → ℂ) :
    ∑ i, ‖(Fin.cons x v : Fin (n + 1) → ℂ) i‖ ^ 2 = ‖x‖ ^ 2 + ∑ j, ‖v j‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The chart lands on the unit sphere, on the closed unit ball of the source. -/
theorem sphereChartVec_mem {n : ℕ} {w : ChartBase n} (hw : chartQ n w ≤ 1) :
    sphereChartVec n w ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff, sphereChartVec, normSq_cons]
  have hnn : 0 ≤ 1 - chartQ n w := by linarith
  have hsq : chartWeight n w ^ 2 = 1 - chartQ n w := by
    rw [chartWeight, Real.sq_sqrt hnn]
  have h0 : ‖(w.1 : ℂ) * Complex.I - (chartWeight n w : ℂ)‖ ^ 2
      = w.1 ^ 2 + chartWeight n w ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [h0, hsq, chartQ]
  ring

theorem continuous_chartQ (n : ℕ) : Continuous (chartQ n) := by
  show Continuous fun w : ChartBase n => w.1 ^ 2 + ∑ j, ‖w.2 j‖ ^ 2
  exact (continuous_fst.pow 2).add (continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_snd).norm.pow 2)

theorem continuous_chartWeight (n : ℕ) : Continuous (chartWeight n) :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_chartQ n))

theorem continuous_sphereChartVec (n : ℕ) : Continuous (sphereChartVec n) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [sphereChartVec, Fin.cons_zero]
    exact ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).sub
      (Complex.continuous_ofReal.comp (continuous_chartWeight n))
  · simp only [sphereChartVec, Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

/-! ## 2. The derivative at the zero, as a continuous linear equivalence -/

/-- **The derivative of the trivial block of the section at its zero**, read in the chart
`(ℝ × (Fin n → ℂ)) × ℝ` of `S^{2n+1} × S¹`: `(dc, dv, du) ↦ Fin.cons (dc·i/2 − du) (dv/2)`. -/
def eulerLinearModel (n : ℕ) : ChartSrc n →ₗ[ℝ] (Fin (n + 1) → ℂ) where
  toFun p := Fin.cons ((p.1.1 : ℂ) * Complex.I / 2 - (p.2 : ℂ)) (fun j => p.1.2 j / 2)
  map_add' p q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.ofReal_add]
        <;> ring
    · simp only [Fin.cons_succ, Prod.fst_add, Prod.snd_add, Pi.add_apply] <;> ring
  map_smul' r p := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Complex.ofReal_mul, Complex.real_smul, RingHom.id_apply] <;> ring
    · simp only [Fin.cons_succ, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
        Complex.real_smul, RingHom.id_apply] <;> ring

@[simp]
theorem eulerLinearModel_apply (n : ℕ) (p : ChartSrc n) :
    eulerLinearModel n p =
      Fin.cons ((p.1.1 : ℂ) * Complex.I / 2 - (p.2 : ℂ)) (fun j => p.1.2 j / 2) := rfl

theorem eulerLinearModel_eq_zero {n : ℕ} {p : ChartSrc n} (h : eulerLinearModel n p = 0) :
    p = 0 := by
  obtain ⟨⟨dc, dv⟩, du⟩ := p
  have h0 : (dc : ℂ) * Complex.I / 2 - (du : ℂ) = 0 := by simpa using congrFun h 0
  have hs : ∀ j, dv j / 2 = 0 := fun j => by simpa using congrFun h j.succ
  have hre : -du = 0 := by
    have := congrArg Complex.re h0
    simpa using this
  have him : dc / 2 = 0 := by
    have := congrArg Complex.im h0
    simpa using this
  have hdu : du = 0 := by linarith
  have hdc : dc = 0 := by linarith
  have hdv : dv = 0 :=
    funext fun j => (div_eq_zero_iff.mp (hs j)).resolve_right (by norm_num)
  simp [Prod.ext_iff, hdu, hdc, hdv]

theorem eulerLinearModel_injective (n : ℕ) : Function.Injective (eulerLinearModel n) := by
  intro p q hpq
  have h : eulerLinearModel n (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  exact sub_eq_zero.mp (eulerLinearModel_eq_zero h)

theorem eulerLinearModel_surjective (n : ℕ) : Function.Surjective (eulerLinearModel n) := by
  intro z
  refine ⟨((2 * (z 0).im, fun j => 2 * z j.succ), -(z 0).re), ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [eulerLinearModel_apply, Fin.cons_zero]
    push_cast
    rw [show ((2 : ℂ) * ((z 0).im : ℂ)) * Complex.I / 2 - (-((z 0).re : ℂ))
        = ((z 0).re : ℂ) + ((z 0).im : ℂ) * Complex.I by ring]
    exact Complex.re_add_im (z 0)
  · simp only [eulerLinearModel_apply, Fin.cons_succ]
    ring

/-- **The derivative is a linear isomorphism**, by the explicit inverse. -/
def eulerLinearEquiv (n : ℕ) : ChartSrc n ≃ₗ[ℝ] (Fin (n + 1) → ℂ) :=
  LinearEquiv.ofBijective (eulerLinearModel n)
    ⟨eulerLinearModel_injective n, eulerLinearModel_surjective n⟩

/-- The derivative as a **continuous** linear equivalence (finite dimensions). -/
def eulerContinuousLinearEquiv (n : ℕ) : ChartSrc n ≃L[ℝ] (Fin (n + 1) → ℂ) :=
  (eulerLinearEquiv n).toContinuousLinearEquiv

@[simp]
theorem eulerContinuousLinearEquiv_apply (n : ℕ) (p : ChartSrc n) :
    eulerContinuousLinearEquiv n p =
      Fin.cons ((p.1.1 : ℂ) * Complex.I / 2 - (p.2 : ℂ)) (fun j => p.1.2 j / 2) := rfl

/-! ## 3. The trivial block in the chart vanishes only at the origin -/

/-- The trivial block of the section, read in the two charts: the circle by its horizontal
coordinate `u`, the sphere by `sphereChartVec n`. -/
def trivialBlockChart (n : ℕ) (w : ChartBase n) (u : ℝ) : Fin (n + 1) → ℂ :=
  fun i => (((1 - (1 + u) / 2 : ℝ)) : ℂ) * eZero n i
    + (((1 + u) / 2 : ℝ) : ℂ) * sphereChartVec n w i

/-- **The zero in the chart is the origin.** -/
theorem trivialBlockChart_eq_zero_iff {n : ℕ} {w : ChartBase n} {u : ℝ}
    (hw : chartQ n w ≤ 1) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    (∀ i, trivialBlockChart n w u i = 0)
      ↔ (u = 0 ∧ ∀ i, sphereChartVec n w i = -eZero n i) := by
  have hτ0 : (0 : ℝ) ≤ (1 + u) / 2 := by linarith
  have hτ1 : (1 + u) / 2 ≤ 1 := by linarith
  have hiff := unitVectors_seam_eq_zero_iff (a := eZero n) (b := sphereChartVec n w)
    (eZero_normSq n) (mem_unitVectors_iff.mp (sphereChartVec_mem hw)) hτ0 hτ1
  constructor
  · intro h
    obtain ⟨hhalf, hneg⟩ := hiff.mp h
    exact ⟨by linarith, hneg⟩
  · rintro ⟨hu, hneg⟩
    exact hiff.mpr ⟨by rw [hu]; norm_num, hneg⟩

/-- The chart is centred at the zero: `(1/2) e₀ + (1/2)(−e₀) = 0`. -/
theorem trivialBlockChart_zero (n : ℕ) : trivialBlockChart n 0 0 = 0 := by
  funext i
  show ((1 - (1 + (0 : ℝ)) / 2 : ℝ) : ℂ) * eZero n i
      + (((1 + (0 : ℝ)) / 2 : ℝ) : ℂ) * sphereChartVec n 0 i = 0
  rw [show sphereChartVec n 0 i = -eZero n i from congrFun (sphereChartVec_zero n) i]
  push_cast
  ring

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.sphereChartVec_mem
#audit_axioms KGen.eulerLinearModel_surjective
#audit_axioms KGen.trivialBlockChart_eq_zero_iff

end GroupApproximation.CharClass
