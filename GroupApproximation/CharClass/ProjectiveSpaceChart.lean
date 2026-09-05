-- Re-proved in the `GroupApproximation.CharClass` namespace from the paused fleet's
-- `GroupApproximation/AlgTop/ComplexProjectiveChart.lean`, which is red at the pin and owned by no
-- lane of the LIX program.  Lane `cc-projective` owns this copy.
import GroupApproximation.CharClass.ProjectiveSpaceBasic

/-!
# The affine chart of `ℂP^d`

The standard affine chart `ℂ^d ≅ {x ∈ ℂP^d : x₀₀ ≠ 0}` of the projection model
(`GroupApproximation/Analysis/LIXProjectiveSpaceModel.lean`, lane `lix-spaces`).

The chart map sends `w : Fin d → ℂ` to the rank-one projection onto the line spanned by
`u = (1, w₁, …, w_d)`. Its entries are

```text
entry (chartAt w) a b = uₐ * star u_b / (1 + ∑ᵢ ‖wᵢ‖²),
```

a *rational* function of `w` and `star w`: the square root hiding inside the
normalization of `u` cancels, because normalizing by the squared norm is exactly what the
idempotent law asks for. That is why continuity of the chart costs nothing here.

## Main results

* `CPn.chartAt`, `CPn.chartInv` — the chart and its inverse `x ↦ (xᵢ₊₁,₀ / x₀₀)ᵢ`;
* `CPn.chartInv_chartAt`, `CPn.chartAt_chartInv` — they are mutually inverse;
* `CPn.isOpen_chartSet` — the chart domain `{x | x₀₀ ≠ 0}` is open;
* `CPn.chartHomeo : (Fin d → ℂ) ≃ₜ ↥(CPn.chartSet d)` — the chart is a homeomorphism.

Since `Fin d → ℂ` is `ℝ`-linearly homeomorphic to `ℝ^{2d}`, this is the open `2d`-cell of
the CW structure of `ℂP^d`; its complement is the hyperplane `ℂP^{d-1}`, built in
`GroupApproximation/AlgTop/ComplexProjectiveHyperplane.lean`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Matrix
open GroupApproximation.STW59

namespace CPn

variable {d : ℕ}

/-! ## 1. Normalizing a vector -/

/-- The squared Euclidean norm of a vector of `ℂ^n`. -/
def sqNorm {n : Type*} [Fintype n] (u : n → ℂ) : ℝ := ∑ k, ‖u k‖ ^ 2

theorem sqNorm_nonneg {n : Type*} [Fintype n] (u : n → ℂ) : 0 ≤ sqNorm u :=
  Finset.sum_nonneg fun k _ => by positivity

theorem sqNorm_pos {n : Type*} [Fintype n] {u : n → ℂ} (hu : sqNorm u ≠ 0) : 0 < sqNorm u :=
  lt_of_le_of_ne (sqNorm_nonneg u) (Ne.symm hu)

/-- `u` rescaled to unit length. -/
def normalize {n : Type*} [Fintype n] (u : n → ℂ) : n → ℂ :=
  fun a => u a / ((Real.sqrt (sqNorm u) : ℝ) : ℂ)

theorem normalize_mem {n : Type*} [Fintype n] {u : n → ℂ} (hu : sqNorm u ≠ 0) :
    normalize u ∈ unitVectors n := by
  have hpos : 0 < sqNorm u := sqNorm_pos hu
  have hs : 0 < Real.sqrt (sqNorm u) := Real.sqrt_pos.mpr hpos
  have hnorm : ‖((Real.sqrt (sqNorm u) : ℝ) : ℂ)‖ = Real.sqrt (sqNorm u) :=
    Complex.norm_of_nonneg hs.le
  show (∑ a, ‖normalize u a‖ ^ 2) = 1
  have hterm : ∀ a, ‖normalize u a‖ ^ 2 = ‖u a‖ ^ 2 / sqNorm u := by
    intro a
    rw [normalize, Complex.norm_div, hnorm, div_pow, Real.sq_sqrt hpos.le]
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div]
  exact div_self hu

/-- The entries of the rank-one projection attached to a normalized vector: the square
root cancels. -/
theorem rankOneProj_normalize {n : Type*} [Fintype n] {u : n → ℂ} (hu : sqNorm u ≠ 0)
    (a b : n) :
    rankOneProj (normalize u) a b = u a * star (u b) / ((sqNorm u : ℝ) : ℂ) := by
  have hpos : 0 < sqNorm u := sqNorm_pos hu
  have hs : ((Real.sqrt (sqNorm u) : ℝ) : ℂ) * ((Real.sqrt (sqNorm u) : ℝ) : ℂ)
      = ((sqNorm u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
  rw [rankOneProj_apply, normalize, star_div₀, Complex.star_def, Complex.conj_ofReal,
    div_mul_div_comm, hs]

/-! ## 2. The chart map -/

/-- The vector `(1, w₁, …, w_d)` spanning the line named by the affine coordinate `w`. -/
def chartVec (w : Fin d → ℂ) : Fin (d + 1) → ℂ := Fin.cons 1 w

@[simp] theorem chartVec_zero (w : Fin d → ℂ) : chartVec w 0 = 1 := Fin.cons_zero _ _

@[simp] theorem chartVec_succ (w : Fin d → ℂ) (i : Fin d) : chartVec w i.succ = w i :=
  Fin.cons_succ _ _ _

theorem chartVec_sqNorm (w : Fin d → ℂ) : sqNorm (chartVec w) = 1 + ∑ i, ‖w i‖ ^ 2 := by
  show (∑ a, ‖chartVec w a‖ ^ 2) = _
  rw [Fin.sum_univ_succ]
  simp

theorem chartVec_sqNorm_pos (w : Fin d → ℂ) : 0 < sqNorm (chartVec w) := by
  rw [chartVec_sqNorm]
  have h : (0:ℝ) ≤ ∑ i, ‖w i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  linarith

theorem chartVec_sqNorm_ne_zero (w : Fin d → ℂ) : sqNorm (chartVec w) ≠ 0 :=
  (chartVec_sqNorm_pos w).ne'

theorem chartDenom_ne_zero (w : Fin d → ℂ) : ((sqNorm (chartVec w) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast chartVec_sqNorm_ne_zero w

/-- The affine chart `ℂ^d → ℂP^d`, `w ↦ [1 : w₁ : ⋯ : w_d]`. -/
def chartAt (w : Fin d → ℂ) : CP d :=
  ⟨rankOneProj (normalize (chartVec w)),
    rankOneProj_mem_cpSet (normalize_mem (chartVec_sqNorm_ne_zero w))⟩

theorem chartAt_entry (w : Fin d → ℂ) (a b : Fin (d + 1)) :
    entry (chartAt w) a b
      = chartVec w a * star (chartVec w b) / ((sqNorm (chartVec w) : ℝ) : ℂ) :=
  rankOneProj_normalize (chartVec_sqNorm_ne_zero w) a b

theorem chartAt_entry_zero_zero (w : Fin d → ℂ) :
    entry (chartAt w) 0 0 = (((sqNorm (chartVec w) : ℝ) : ℂ))⁻¹ := by
  rw [chartAt_entry, chartVec_zero]
  simp

theorem chartAt_entry_zero_zero_ne_zero (w : Fin d → ℂ) : entry (chartAt w) 0 0 ≠ 0 := by
  rw [chartAt_entry_zero_zero]
  simpa only [ne_eq, inv_eq_zero] using chartDenom_ne_zero w

theorem chartAt_entry_succ_zero (w : Fin d → ℂ) (i : Fin d) :
    entry (chartAt w) i.succ 0 = w i / ((sqNorm (chartVec w) : ℝ) : ℂ) := by
  rw [chartAt_entry, chartVec_zero, chartVec_succ]
  simp

/-! ## 3. Continuity of the chart map -/

theorem continuous_chartVec (a : Fin (d + 1)) :
    Continuous fun w : Fin d → ℂ => chartVec w a := by
  refine Fin.cases ?_ ?_ a
  · simpa only [chartVec_zero] using continuous_const
  · intro i
    simpa only [chartVec_succ] using continuous_apply i

theorem continuous_chartDenom :
    Continuous fun w : Fin d → ℂ => ((sqNorm (chartVec w) : ℝ) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  show Continuous fun w : Fin d → ℂ => ∑ k, ‖chartVec w k‖ ^ 2
  exact continuous_finsetSum _ fun k _ => ((continuous_chartVec k).norm).pow 2

theorem continuous_chartAt_entry (a b : Fin (d + 1)) :
    Continuous fun w : Fin d → ℂ => entry (chartAt w) a b := by
  have hfun : (fun w : Fin d → ℂ => entry (chartAt w) a b)
      = fun w => chartVec w a * star (chartVec w b) / ((sqNorm (chartVec w) : ℝ) : ℂ) :=
    funext fun w => chartAt_entry w a b
  rw [hfun]
  exact Continuous.div ((continuous_chartVec a).mul ((continuous_chartVec b).star))
    continuous_chartDenom chartDenom_ne_zero

theorem continuous_chartAt : Continuous (chartAt (d := d)) := by
  apply Continuous.subtype_mk
  exact continuous_matrix fun a b => continuous_chartAt_entry a b

/-! ## 4. The chart domain and the inverse chart -/

/-- The domain of the affine chart: the points whose `(0,0)` entry does not vanish, i.e.
the lines not contained in the hyperplane `z₀ = 0`. -/
def chartSet (d : ℕ) : Set (CP d) := {x | entry x 0 0 ≠ 0}

theorem mem_chartSet {x : CP d} : x ∈ chartSet d ↔ entry x 0 0 ≠ 0 := Iff.rfl

theorem isOpen_chartSet : IsOpen (chartSet d) :=
  (continuous_entry (d := d) 0 0).isOpen_preimage {0}ᶜ isOpen_compl_singleton

theorem chartAt_mem_chartSet (w : Fin d → ℂ) : chartAt w ∈ chartSet d :=
  chartAt_entry_zero_zero_ne_zero w

/-- The inverse of the affine chart: the affine coordinates of a line not contained in
the hyperplane `z₀ = 0`. -/
def chartInv (x : CP d) : Fin d → ℂ := fun i => entry x i.succ 0 / entry x 0 0

theorem chartInv_chartAt (w : Fin d → ℂ) : chartInv (chartAt w) = w := by
  funext i
  show entry (chartAt w) i.succ 0 / entry (chartAt w) 0 0 = w i
  rw [chartAt_entry_succ_zero, chartAt_entry_zero_zero]
  have hS := chartDenom_ne_zero w
  field_simp

/-- On the chart domain the affine coordinates determine the point. -/
theorem chartAt_chartInv (x : CP d) (hx : entry x 0 0 ≠ 0) : chartAt (chartInv x) = x := by
  set r : ℝ := ∑ k, ‖entry x k 0‖ ^ 2 with hrdef
  have hrnn : (0:ℝ) ≤ r := Finset.sum_nonneg fun k _ => by positivity
  have hr : entry x 0 0 = (r : ℂ) := entry_diag x 0
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr]; exact hx
  have hrR : r ≠ 0 := by exact_mod_cast hr0
  -- the chart vector of the affine coordinates is the `0`-th column, scaled by `r`
  have hvec : ∀ a, chartVec (chartInv x) a = entry x a 0 / (r : ℂ) := by
    intro a
    refine Fin.cases ?_ ?_ a
    · rw [chartVec_zero, ← hr]
      exact (div_self hx).symm
    · intro i
      rw [chartVec_succ]
      show entry x i.succ 0 / entry x 0 0 = entry x i.succ 0 / (r : ℂ)
      rw [hr]
  -- its squared norm is `1 / r`
  have hsum : sqNorm (chartVec (chartInv x)) = 1 / r := by
    show (∑ c, ‖chartVec (chartInv x) c‖ ^ 2) = 1 / r
    have hterm : ∀ c, ‖chartVec (chartInv x) c‖ ^ 2 = ‖entry x c 0‖ ^ 2 / (r * r) := by
      intro c
      rw [hvec c, Complex.norm_div, Complex.norm_of_nonneg hrnn, div_pow, sq]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_div, ← hrdef]
    field_simp
  refine ext fun a b => ?_
  rw [chartAt_entry, hvec a, hvec b, hsum]
  have hstar : star (entry x b 0 / (r : ℂ)) = entry x 0 b / (r : ℂ) := by
    simp only [Complex.star_def, map_div₀, Complex.conj_ofReal, entry_conj]
  have hminor : entry x a 0 * entry x 0 b = (r : ℂ) * entry x a b := by
    rw [← hr]; exact entry_minor x a b 0
  rw [hstar]
  have hone : ((1 / r : ℝ) : ℂ) = 1 / (r : ℂ) := by push_cast; ring
  rw [hone]
  field_simp
  linear_combination hminor

/-! ## 5. The chart as a homeomorphism -/

theorem continuous_chartInv_on :
    Continuous fun x : ↥(chartSet d) => chartInv (x : CP d) := by
  refine continuous_pi fun i => ?_
  exact Continuous.div ((continuous_entry i.succ 0).comp continuous_subtype_val)
    ((continuous_entry (0 : Fin (d + 1)) 0).comp continuous_subtype_val) fun x => x.2

/-- **The affine chart is a homeomorphism** `ℂ^d ≃ₜ {x ∈ ℂP^d : x₀₀ ≠ 0}`.
This is the open `2d`-cell of the CW structure of `ℂP^d`. -/
def chartHomeo (d : ℕ) : (Fin d → ℂ) ≃ₜ ↥(chartSet d) where
  toFun w := ⟨chartAt w, chartAt_mem_chartSet w⟩
  invFun x := chartInv (x : CP d)
  left_inv w := chartInv_chartAt w
  right_inv x := Subtype.ext (chartAt_chartInv (x : CP d) x.2)
  continuous_toFun := continuous_chartAt.subtype_mk _
  continuous_invFun := continuous_chartInv_on

@[simp] theorem chartHomeo_apply (w : Fin d → ℂ) :
    ((chartHomeo d w : ↥(chartSet d)) : CP d) = chartAt w := rfl

@[simp] theorem chartHomeo_symm_apply (x : ↥(chartSet d)) :
    (chartHomeo d).symm x = chartInv (x : CP d) := rfl

/-- The base point is the chart's origin. -/
theorem chartAt_zero (d : ℕ) : chartAt (0 : Fin d → ℂ) = basePoint d := by
  refine ext fun a b => ?_
  have hden : sqNorm (chartVec (0 : Fin d → ℂ)) = 1 := by
    rw [chartVec_sqNorm]
    simp
  rw [chartAt_entry, hden, basePoint_entry]
  have hv : ∀ c : Fin (d + 1), chartVec (0 : Fin d → ℂ) c = baseVec d c := by
    intro c
    refine Fin.cases ?_ ?_ c
    · rw [chartVec_zero, baseVec_zero]
    · intro i
      rw [chartVec_succ, baseVec_apply_of_ne (Fin.succ_ne_zero i)]
      rfl
  rw [hv a, hv b]
  simp

end CPn

end GroupApproximation.CharClass
