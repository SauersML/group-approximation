import GroupApproximation.AlgTop.ComplexProjectiveBasic

/-!
# The affine chart of `ℂP^d`

The standard affine chart `ℂ^d ≅ {x ∈ ℂP^d : x₀₀ ≠ 0}` of the projection model of
`GroupApproximation/AlgTop/ComplexProjectiveBasic.lean`.

The chart map sends `w : Fin d → ℂ` to the rank-one projection onto the line spanned by
`(1, w₁, …, w_d)`, that is, to the matrix

```text
(chartAt w) a b = uₐ * conj u_b / (1 + ‖w‖²),   u = Fin.cons 1 w.
```

No square roots appear: normalizing by the *squared* norm is exactly what makes the
matrix idempotent, so the chart map is a rational function of `w` and `conj w`.

## Main results

* `CP.chartAt`, `CP.chartInv` — the chart and its inverse `x ↦ (xᵢ₊₁,₀ / x₀₀)ᵢ`;
* `CP.chartInv_chartAt`, `CP.chartAt_chartInv` — they are mutually inverse;
* `CP.isOpen_chartSet` — the chart domain `{x | x₀₀ ≠ 0}` is open;
* `CP.chartHomeo : (Fin d → ℂ) ≃ₜ ↥(CP.chartSet d)` — the chart is a homeomorphism.

Since `Fin d → ℂ` is `ℝ`-linearly homeomorphic to `ℝ^{2d}`, this is the `2d`-cell of the
CW structure of `ℂP^d`; its complement is the hyperplane `ℂP^{d-1}`, built in
`GroupApproximation/AlgTop/ComplexProjectiveHyperplane.lean`.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix Complex
open scoped ComplexConjugate

namespace CP

variable {d : ℕ}

/-! ## 1. Projections from arbitrary nonzero vectors -/

/-- The normalized outer product `u uᴴ / ‖u‖²` is a rank-one projection for every vector
`u` of nonzero norm. No square root is taken: the normalization is by the *squared* norm,
which is exactly what the idempotent law asks for. -/
theorem isLineProj_outerScaled {m : ℕ} (u : Fin (m + 1) → ℂ)
    (hu : (∑ a, Complex.normSq (u a)) ≠ 0) :
    IsLineProj (Matrix.of fun a b =>
      u a * conj (u b) / ((∑ c, Complex.normSq (u c) : ℝ) : ℂ)) := by
  set S : ℂ := ((∑ c, Complex.normSq (u c) : ℝ) : ℂ) with hSdef
  have hS : S ≠ 0 := by
    rw [hSdef]
    exact_mod_cast hu
  have hSconj : conj S = S := by rw [hSdef]; exact Complex.conj_ofReal _
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, map_div₀, map_mul,
      Complex.conj_conj, hSconj]
    ring
  · ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hterm : ∀ c, u a * conj (u c) / S * (u c * conj (u b) / S)
        = (u a * conj (u b) / (S * S)) * ((Complex.normSq (u c) : ℝ) : ℂ) := by
      intro c
      rw [Complex.normSq_eq_conj_mul_self]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← Complex.ofReal_sum, ← hSdef]
    field_simp
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    have hterm : ∀ a, u a * conj (u a) / S = ((Complex.normSq (u a) : ℝ) : ℂ) / S := by
      intro a; rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div, ← Complex.ofReal_sum, ← hSdef]
    exact div_self hS

/-! ## 2. The chart map -/

/-- The vector `(1, w₁, …, w_d)` spanning the line named by the affine coordinate `w`. -/
def chartVec (w : Fin d → ℂ) : Fin (d + 1) → ℂ := Fin.cons 1 w

@[simp] theorem chartVec_zero (w : Fin d → ℂ) : chartVec w 0 = 1 := Fin.cons_zero _ _

@[simp] theorem chartVec_succ (w : Fin d → ℂ) (i : Fin d) : chartVec w i.succ = w i :=
  Fin.cons_succ _ _ _

theorem chartVec_sum (w : Fin d → ℂ) :
    (∑ a, Complex.normSq (chartVec w a)) = 1 + ∑ i, Complex.normSq (w i) := by
  rw [Fin.sum_univ_succ]
  simp

theorem chartVec_sum_pos (w : Fin d → ℂ) : (0:ℝ) < ∑ a, Complex.normSq (chartVec w a) := by
  rw [chartVec_sum]
  have : (0:ℝ) ≤ ∑ i, Complex.normSq (w i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  linarith

theorem chartVec_sum_ne_zero (w : Fin d → ℂ) : (∑ a, Complex.normSq (chartVec w a)) ≠ 0 :=
  (chartVec_sum_pos w).ne'

/-- The affine chart `ℂ^d → ℂP^d`, `w ↦ [1 : w₁ : ⋯ : w_d]`. -/
def chartAt (w : Fin d → ℂ) : CP d :=
  ⟨Matrix.of fun a b =>
      chartVec w a * conj (chartVec w b) / ((∑ c, Complex.normSq (chartVec w c) : ℝ) : ℂ),
    isLineProj_outerScaled (chartVec w) (chartVec_sum_ne_zero w)⟩

@[simp] theorem chartAt_mat (w : Fin d → ℂ) (a b : Fin (d + 1)) :
    (chartAt w).mat a b =
      chartVec w a * conj (chartVec w b) / ((∑ c, Complex.normSq (chartVec w c) : ℝ) : ℂ) :=
  rfl

theorem chartAt_mat_zero_zero (w : Fin d → ℂ) :
    (chartAt w).mat 0 0 = (((∑ c, Complex.normSq (chartVec w c) : ℝ) : ℂ))⁻¹ := by
  rw [chartAt_mat, chartVec_zero]
  simp

theorem chartAt_mat_zero_zero_ne_zero (w : Fin d → ℂ) : (chartAt w).mat 0 0 ≠ 0 := by
  rw [chartAt_mat_zero_zero]
  simp only [ne_eq, inv_eq_zero]
  exact_mod_cast chartVec_sum_ne_zero w

theorem chartAt_mat_succ_zero (w : Fin d → ℂ) (i : Fin d) :
    (chartAt w).mat i.succ 0 = w i / ((∑ c, Complex.normSq (chartVec w c) : ℝ) : ℂ) := by
  rw [chartAt_mat, chartVec_zero, chartVec_succ]
  simp

/-! ## 3. Continuity of the chart map -/

theorem continuous_chartVec (a : Fin (d + 1)) :
    Continuous fun w : Fin d → ℂ => chartVec w a := by
  refine Fin.cases ?_ ?_ a
  · simpa only [chartVec_zero] using continuous_const
  · intro i
    simpa only [chartVec_succ] using continuous_apply i

theorem continuous_chartDenom :
    Continuous fun w : Fin d → ℂ => ((∑ c, Complex.normSq (chartVec w c) : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (continuous_finsetSum _ fun c _ => Complex.continuous_normSq.comp (continuous_chartVec c))

theorem continuous_chartAt : Continuous (chartAt (d := d)) := by
  apply Continuous.subtype_mk
  refine continuous_matrix fun a b => ?_
  refine Continuous.div (((continuous_chartVec a).mul
    (Complex.continuous_conj.comp (continuous_chartVec b)))) continuous_chartDenom ?_
  intro w
  exact_mod_cast chartVec_sum_ne_zero w

/-! ## 4. The chart domain and the inverse chart -/

/-- The domain of the affine chart: the points whose `(0,0)` entry does not vanish, i.e.
those lines not contained in the hyperplane `z₀ = 0`. -/
def chartSet (d : ℕ) : Set (CP d) := {x | x.mat 0 0 ≠ 0}

theorem mem_chartSet {x : CP d} : x ∈ chartSet d ↔ x.mat 0 0 ≠ 0 := Iff.rfl

theorem isOpen_chartSet : IsOpen (chartSet d) :=
  (continuous_entry 0 0).isOpen_preimage {0}ᶜ isOpen_compl_singleton

theorem chartAt_mem_chartSet (w : Fin d → ℂ) : chartAt w ∈ chartSet d :=
  chartAt_mat_zero_zero_ne_zero w

/-- The inverse of the affine chart: the affine coordinates of a line not contained in
the hyperplane `z₀ = 0`. -/
def chartInv (x : CP d) : Fin d → ℂ := fun i => x.mat i.succ 0 / x.mat 0 0

theorem chartInv_chartAt (w : Fin d → ℂ) : chartInv (chartAt w) = w := by
  funext i
  rw [chartInv, chartAt_mat_succ_zero, chartAt_mat_zero_zero]
  have hS : ((∑ c, Complex.normSq (chartVec w c) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast chartVec_sum_ne_zero w
  field_simp

/-- On the chart domain the affine coordinates determine the point. -/
theorem chartAt_chartInv (x : CP d) (hx : x.mat 0 0 ≠ 0) : chartAt (chartInv x) = x := by
  set r : ℝ := ∑ c, Complex.normSq (x.mat c 0) with hrdef
  have hr : x.mat 0 0 = (r : ℂ) := x.prop.diag_eq 0
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr]; exact hx
  have hrR : r ≠ 0 := by exact_mod_cast hr0
  -- the chart vector of the affine coordinates is the `0`-th column, scaled by `r`
  have hvec : ∀ a, chartVec (chartInv x) a = x.mat a 0 / (r : ℂ) := by
    intro a
    refine Fin.cases ?_ ?_ a
    · rw [chartVec_zero, ← hr]
      field_simp
    · intro i
      rw [chartVec_succ, chartInv, hr]
  -- its squared norm is `1 / r`
  have hsum : (∑ c, Complex.normSq (chartVec (chartInv x) c)) = 1 / r := by
    have : ∀ c, Complex.normSq (chartVec (chartInv x) c)
        = Complex.normSq (x.mat c 0) / (r * r) := by
      intro c
      rw [hvec c, Complex.normSq_div, Complex.normSq_ofReal]
    rw [Finset.sum_congr rfl fun c _ => this c, ← Finset.sum_div, ← hrdef]
    field_simp
  refine ext ?_
  funext a b
  rw [chartAt_mat, hvec a, hvec b, hsum]
  have hconj : conj (x.mat b 0 / (r : ℂ)) = x.mat 0 b / (r : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal, x.prop.conj_entry b 0]
  rw [hconj]
  have hminor : x.mat a 0 * x.mat 0 b = (r : ℂ) * x.mat a b := by
    rw [← hr]; exact x.prop.minor a b 0
  have hone : ((1 / r : ℝ) : ℂ) = 1 / (r : ℂ) := by push_cast; ring
  rw [hone]
  field_simp
  rw [hminor]
  ring

/-! ## 5. The chart as a homeomorphism -/

theorem continuous_chartInv_on :
    Continuous fun x : ↥(chartSet d) => chartInv x.1 := by
  refine continuous_pi fun i => ?_
  exact Continuous.div (((continuous_entry i.succ 0).comp continuous_subtype_val))
    (((continuous_entry (0 : Fin (d + 1)) 0).comp continuous_subtype_val)) fun x => x.2

/-- **The affine chart is a homeomorphism** `ℂ^d ≃ₜ {x ∈ ℂP^d : x₀₀ ≠ 0}`.
This is the top cell of the CW structure of `ℂP^d`. -/
def chartHomeo (d : ℕ) : (Fin d → ℂ) ≃ₜ ↥(chartSet d) where
  toFun w := ⟨chartAt w, chartAt_mem_chartSet w⟩
  invFun x := chartInv x.1
  left_inv w := chartInv_chartAt w
  right_inv x := Subtype.ext (chartAt_chartInv x.1 x.2)
  continuous_toFun := continuous_chartAt.subtype_mk _
  continuous_invFun := continuous_chartInv_on

@[simp] theorem chartHomeo_apply (w : Fin d → ℂ) : (chartHomeo d w : CP d) = chartAt w := rfl

@[simp] theorem chartHomeo_symm_apply (x : ↥(chartSet d)) :
    (chartHomeo d).symm x = chartInv x.1 := rfl

end CP

end GroupApproximation.AlgTop
