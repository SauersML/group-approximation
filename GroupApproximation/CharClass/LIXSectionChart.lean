import GroupApproximation.CharClass.LIXSectionManuscript

/-!
# Charts at the zero, and the linear model of the section there

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXSectionManuscript.lean` shows the manuscript's section of the mapping torus
has exactly one zero.  `cc-thom`'s `EulerLocalChart.openPartialHomeomorphChartPair`
converts "the section is a local homeomorphism at that zero" into the homeomorphism of
pairs its Thom-class layer consumes, and the local homeomorphism itself is to come from
`HasStrictFDerivAt.toOpenPartialHomeomorph`.  That theorem needs the source to be a
**normed vector space**, so the section has to be read in charts first.

## The chart that avoids `EuclideanSpace`

`S⁵` here is `STW59.unitVectors (Fin 3)`, a subset of the sup-normed function space
`Fin 3 → ℂ`, whereas `AlgTop/EulerLocalModel.lean`'s `eulerLocalModelEquiv` is stated for a
real inner product space and for an orthogonal-complement submodule.  Bridging would mean
`EuclideanSpace ℂ (Fin 3)`, the `InnerProductSpace.complexToReal` instance and a transport
across `WithLp`, which at this pin is a *structure* and so not definitionally the function
type.

None of that is needed.  The real tangent space of `S⁵` at `-e₃` is `{ξ : re ξ₂ = 0}`, and

```text
sphereChartVec (u, v, c) = ![u, v, c·i − √(1 − (‖u‖² + ‖v‖² + c²))]
```

parametrises a neighbourhood of `-e₃` by the plain product `ℂ × ℂ × ℝ`, five real
dimensions, with no submodule anywhere.  Together with the circle coordinate the source is
`(ℂ × ℂ × ℝ) × ℝ`, six real dimensions, matching `ℂ³`.

## The derivative, written down

With `τ = (1 + y)/2` the trivial block of the section is `(1−τ) e₃ + τ x`, and since the
square root has vanishing differential at the origin, its derivative there is

```text
(du, dv, dc, dy) ↦ (du/2, dv/2, (dc/2)·i − dy),
```

which is `eulerLinearModel` below.  `eulerLinearEquiv` proves it bijective by exhibiting
the inverse, so no determinant, no orientation and no appeal to
`eulerLocalModelEquiv` is required — that module remains a cross-check rather than a
dependency.

## Main results

* `sphereChartVec`, `sphereChart` — the chart of `S⁵` at `-e₃`, with `sphereChart_zero`.
* `eulerLinearModel`, `eulerLinearEquiv`, `eulerContinuousLinearEquiv` — the derivative at
  the zero, as a continuous linear equivalence.
* `trivialBlockChart_eq_zero_iff` — in the chart, the trivial block of the section
  vanishes only at the origin.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The chart of `S⁵` at `-e₃` -/

/-- The radial weight of the chart: `√(1 − ‖w‖²)`. -/
def chartWeight (w : ℂ × ℂ × ℝ) : ℝ :=
  Real.sqrt (1 - (‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2))

/-- **The chart of `S⁵` at `-e₃`**, with source the plain product `ℂ × ℂ × ℝ`.  The third
coordinate is purely imaginary plus the radial correction, which is exactly the real
tangent space `{ξ : re ξ₂ = 0}` of the sphere at `-e₃`. -/
def sphereChartVec (w : ℂ × ℂ × ℝ) : Fin 3 → ℂ :=
  ![w.1, w.2.1, (w.2.2 : ℂ) * Complex.I - (chartWeight w : ℂ)]

@[simp]
theorem sphereChartVec_zero : sphereChartVec 0 = fun i => -eThree i := by
  funext i
  fin_cases i <;>
    simp [sphereChartVec, chartWeight, eThree]

/-- The chart really lands on the unit sphere, for `w` in the closed unit ball of the
source. -/
theorem sphereChartVec_mem {w : ℂ × ℂ × ℝ}
    (hw : ‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2 ≤ 1) :
    sphereChartVec w ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, Fin.sum_univ_three]
  have hnn : 0 ≤ 1 - (‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2) := by linarith
  have hsq : chartWeight w ^ 2 = 1 - (‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2) := by
    rw [chartWeight, Real.sq_sqrt hnn]
  have h2 : ‖(w.2.2 : ℂ) * Complex.I - (chartWeight w : ℂ)‖ ^ 2
      = w.2.2 ^ 2 + chartWeight w ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  simp only [sphereChartVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [h2, hsq]
  ring

/-- The chart, as a map into the sphere. -/
def sphereChart {w : ℂ × ℂ × ℝ} (hw : ‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2 ≤ 1) :
    ↥(unitVectors (Fin 3)) :=
  ⟨sphereChartVec w, sphereChartVec_mem hw⟩

theorem sphereChart_zero :
    sphereChart (w := 0) (by norm_num) = negEThree := by
  refine Subtype.ext ?_
  rw [sphereChart, negEThree]
  exact sphereChartVec_zero

theorem continuous_sphereChartVec : Continuous sphereChartVec := by
  have hq : Continuous fun w : ℂ × ℂ × ℝ => ‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2 :=
    (((continuous_norm.comp continuous_fst).pow 2).add
      ((continuous_norm.comp (continuous_fst.comp continuous_snd)).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2)
  have hw : Continuous chartWeight := Real.continuous_sqrt.comp (continuous_const.sub hq)
  refine continuous_pi fun i => ?_
  fin_cases i
  · have h : Continuous fun a : ℂ × ℂ × ℝ => a.1 := continuous_fst
    simpa [sphereChartVec] using h
  · have h : Continuous fun a : ℂ × ℂ × ℝ => a.2.1 := continuous_fst.comp continuous_snd
    simpa [sphereChartVec] using h
  · have h : Continuous fun a : ℂ × ℂ × ℝ =>
        ((a.2.2 : ℝ) : ℂ) * Complex.I - ((chartWeight a : ℝ) : ℂ) :=
      ((Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd)).mul
        continuous_const).sub (Complex.continuous_ofReal.comp hw)
    simpa [sphereChartVec] using h

/-! ## 2. The derivative at the zero, as a continuous linear equivalence -/

/-- **The derivative of the trivial block of the section at its zero**, read in the chart
`(ℂ × ℂ × ℝ) × ℝ` of `S⁵ × S¹`:

```text
(du, dv, dc, dy) ↦ (du/2, dv/2, (dc/2)·i − dy).
```

The `1/2` comes from `τ = 1/2` at the zero and the `−dy` from `dτ = dy/2` against the
manuscript's `−2 a e₃`. -/
def eulerLinearModel : ((ℂ × ℂ × ℝ) × ℝ) →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun p := ![p.1.1 / 2, p.1.2.1 / 2, ((p.1.2.2 : ℂ) * Complex.I) / 2 - (p.2 : ℂ)]
  map_add' p q := by
    funext i
    fin_cases i <;> · simp; ring
  map_smul' r p := by
    funext i
    fin_cases i <;> · simp; ring

@[simp]
theorem eulerLinearModel_apply (p : (ℂ × ℂ × ℝ) × ℝ) :
    eulerLinearModel p =
      ![p.1.1 / 2, p.1.2.1 / 2, ((p.1.2.2 : ℂ) * Complex.I) / 2 - (p.2 : ℂ)] := rfl

theorem eulerLinearModel_eq_zero {p : (ℂ × ℂ × ℝ) × ℝ} (h : eulerLinearModel p = 0) :
    p = 0 := by
  obtain ⟨⟨du, dv, dc⟩, dy⟩ := p
  have h0 : du / 2 = 0 := by simpa using congrFun h 0
  have h1 : dv / 2 = 0 := by simpa using congrFun h 1
  have h2 : ((dc : ℂ) * Complex.I) / 2 - (dy : ℂ) = 0 := by simpa using congrFun h 2
  have hdu : du = 0 := (div_eq_zero_iff.mp h0).resolve_right (by norm_num)
  have hdv : dv = 0 := (div_eq_zero_iff.mp h1).resolve_right (by norm_num)
  have hre : -dy = 0 := by
    have := congrArg Complex.re h2
    simpa using this
  have him : dc / 2 = 0 := by
    have := congrArg Complex.im h2
    simpa using this
  have hdy : dy = 0 := by linarith
  have hdc : dc = 0 := by linarith
  simp [Prod.ext_iff, hdu, hdv, hdc, hdy]

theorem eulerLinearModel_injective : Function.Injective eulerLinearModel := by
  intro p q hpq
  have h : eulerLinearModel (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  exact sub_eq_zero.mp (eulerLinearModel_eq_zero h)

theorem eulerLinearModel_surjective : Function.Surjective eulerLinearModel := by
  intro z
  refine ⟨((2 * z 0, 2 * z 1, 2 * (z 2).im), -(z 2).re), ?_⟩
  funext i
  fin_cases i
  · simp
  · simp
  · simp only [eulerLinearModel_apply]
    push_cast
    rw [show ((2 : ℂ) * ((z 2).im : ℂ)) * Complex.I / 2 - (-((z 2).re : ℂ))
        = ((z 2).re : ℂ) + ((z 2).im : ℂ) * Complex.I by ring]
    exact Complex.re_add_im (z 2)

/-- **The derivative is a linear isomorphism.**  Proved by exhibiting the inverse, so no
orientation, determinant or inner product enters. -/
def eulerLinearEquiv : ((ℂ × ℂ × ℝ) × ℝ) ≃ₗ[ℝ] (Fin 3 → ℂ) :=
  LinearEquiv.ofBijective eulerLinearModel
    ⟨eulerLinearModel_injective, eulerLinearModel_surjective⟩

/-- The derivative as a **continuous** linear equivalence, which is the form
`HasStrictFDerivAt.toOpenPartialHomeomorph` consumes.  Both sides are
finite-dimensional over `ℝ`, so continuity is automatic. -/
def eulerContinuousLinearEquiv : ((ℂ × ℂ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℂ) :=
  eulerLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem eulerContinuousLinearEquiv_apply (p : (ℂ × ℂ × ℝ) × ℝ) :
    eulerContinuousLinearEquiv p =
      ![p.1.1 / 2, p.1.2.1 / 2, ((p.1.2.2 : ℂ) * Complex.I) / 2 - (p.2 : ℂ)] := rfl

/-! ## 3. The trivial block in the chart vanishes only at the origin -/

/-- The trivial block of the manuscript's section, read in the two charts: the circle by
its horizontal coordinate `u`, the sphere by `sphereChartVec`. -/
def trivialBlockChart (w : ℂ × ℂ × ℝ) (u : ℝ) : Fin 3 → ℂ :=
  fun i => (((1 - (1 + u) / 2 : ℝ)) : ℂ) * eThree i
    + (((1 + u) / 2 : ℝ) : ℂ) * sphereChartVec w i

/-- **The zero in the chart is the origin.**  A restatement of
`unitVectors_seam_eq_zero_iff` in the chart coordinates, which is the input the local
homeomorphism statement consumes: the section, read in charts, vanishes only at `0`. -/
theorem trivialBlockChart_eq_zero_iff {w : ℂ × ℂ × ℝ} {u : ℝ}
    (hw : ‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2 ≤ 1) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    (∀ i, trivialBlockChart w u i = 0)
      ↔ (u = 0 ∧ ∀ i, sphereChartVec w i = -eThree i) := by
  have hτ0 : (0 : ℝ) ≤ (1 + u) / 2 := by linarith
  have hτ1 : (1 + u) / 2 ≤ 1 := by linarith
  have hiff := unitVectors_seam_eq_zero_iff (a := eThree) (b := sphereChartVec w)
    eThree_normSq (mem_unitVectors_iff.mp (sphereChartVec_mem hw)) hτ0 hτ1
  constructor
  · intro h
    obtain ⟨hhalf, hneg⟩ := hiff.mp h
    refine ⟨by linarith, hneg⟩
  · rintro ⟨hu, hneg⟩
    refine hiff.mpr ⟨by rw [hu]; norm_num, hneg⟩

end GroupApproximation.CharClass
