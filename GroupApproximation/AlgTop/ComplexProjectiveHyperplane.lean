import GroupApproximation.AlgTop.ComplexProjectiveChart

/-!
# The hyperplane `ℂP^d ⊂ ℂP^{d+1}`

The linear hyperplane `z₀ = 0` inside `ℂ^{d+2}` gives a copy of `ℂP^d` inside `ℂP^{d+1}`.
In the projection model of `GroupApproximation/AlgTop/ComplexProjectiveBasic.lean` this is
the map that pads a rank-one projection by a zero row and a zero column:

```text
incl x = ⎛ 0  0 ⎞
         ⎝ 0  x ⎠.
```

## Main results

* `CP.incl : CP d → CP (d+1)` and its entry description;
* `CP.isClosedEmbedding_incl` — it is a closed topological embedding (continuous and
  injective out of a compact space into a Hausdorff space);
* `CP.range_incl : Set.range incl = {y | y.mat 0 0 = 0}` — the image is exactly the
  complement of the affine chart `CP.chartSet (d+1)`;
* `CP.chartSet_eq_compl_range_incl` — the chart and the hyperplane partition `ℂP^{d+1}`.

Together with `GroupApproximation/AlgTop/ComplexProjectiveChart.lean` this is the cell
decomposition step: `ℂP^{d+1}` is `ℂP^d` with one `2(d+1)`-cell attached, the cell being
the affine chart `ℂ^{d+1}`. Since all cells are even-dimensional, every cellular boundary
map of `ℂP^n` vanishes.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix Complex
open scoped ComplexConjugate

/-- If a diagonal entry of a rank-one projection vanishes, so does the whole
corresponding row. -/
theorem IsLineProj.row_eq_zero_of_diag_eq_zero {n : Type*} [Fintype n] {q : Matrix n n ℂ}
    (h : IsLineProj q) {j : n} (hj : q j j = 0) (c : n) : q j c = 0 := by
  have hcol := h.col_eq_zero_of_diag_eq_zero hj c
  have hconj := h.conj_entry c j
  rw [hcol] at hconj
  simpa using hconj.symm

namespace CP

variable {d : ℕ}

/-! ## 1. The padded matrix -/

/-- The matrix of `x : CP d` padded by a zero row and a zero column. -/
def inclMat (x : CP d) : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ :=
  Matrix.of (Fin.cons 0 fun i => Fin.cons 0 (x.mat i))

@[simp] theorem inclMat_zero_row (x : CP d) (b : Fin (d + 2)) : inclMat x 0 b = 0 := by
  simp [inclMat]

@[simp] theorem inclMat_succ_zero (x : CP d) (i : Fin (d + 1)) : inclMat x i.succ 0 = 0 := by
  simp [inclMat]

@[simp] theorem inclMat_succ_succ (x : CP d) (i j : Fin (d + 1)) :
    inclMat x i.succ j.succ = x.mat i j := by
  simp [inclMat]

@[simp] theorem inclMat_zero_col (x : CP d) (a : Fin (d + 2)) : inclMat x a 0 = 0 := by
  refine Fin.cases ?_ ?_ a <;> simp

theorem isLineProj_inclMat (x : CP d) : IsLineProj (inclMat x) := by
  refine ⟨?_, ?_, ?_⟩
  · refine Matrix.ext fun a b => ?_
    rw [Matrix.conjTranspose_apply]
    refine Fin.cases ?_ ?_ a
    · refine Fin.cases ?_ ?_ b <;> intros <;> simp
    · intro i
      refine Fin.cases ?_ ?_ b
      · simp
      · intro j
        rw [inclMat_succ_succ, inclMat_succ_succ, Complex.star_def, x.prop.conj_entry]
  · refine Matrix.ext fun a b => ?_
    rw [Matrix.mul_apply]
    refine Fin.cases ?_ ?_ a
    · simp
    · intro i
      refine Fin.cases ?_ ?_ b
      · simp
      · intro j
        rw [Fin.sum_univ_succ]
        simp only [inclMat_succ_zero, inclMat_zero_row, zero_mul, inclMat_succ_succ, zero_add]
        exact x.prop.sum_mul i j
  · simp only [Matrix.trace, Matrix.diag_apply]
    rw [Fin.sum_univ_succ]
    simp only [inclMat_zero_row, inclMat_succ_succ, zero_add]
    have := x.prop.trace_eq
    simpa only [Matrix.trace, Matrix.diag_apply] using this

/-- **The hyperplane inclusion** `ℂP^d ↪ ℂP^{d+1}`, `[z₁ : ⋯ : z_{d+1}] ↦ [0 : z₁ : ⋯ : z_{d+1}]`. -/
def incl (x : CP d) : CP (d + 1) := ⟨inclMat x, isLineProj_inclMat x⟩

@[simp] theorem incl_mat (x : CP d) : (incl x).mat = inclMat x := rfl

@[simp] theorem incl_mat_zero_zero (x : CP d) : (incl x).mat 0 0 = 0 := by simp

/-! ## 2. `incl` is a closed embedding -/

theorem continuous_incl : Continuous (incl (d := d)) := by
  apply Continuous.subtype_mk
  refine continuous_matrix fun a b => ?_
  refine Fin.cases ?_ ?_ a
  · simpa only [inclMat_zero_row] using continuous_const
  · intro i
    refine Fin.cases ?_ ?_ b
    · simpa only [inclMat_succ_zero] using continuous_const
    · intro j
      simpa only [inclMat_succ_succ] using continuous_entry i j

theorem injective_incl : Function.Injective (incl (d := d)) := by
  intro x y hxy
  refine ext (Matrix.ext fun i j => ?_)
  have := Matrix.ext_iff.2 (congrArg CP.mat hxy) i.succ j.succ
  simpa only [incl_mat, inclMat_succ_succ] using this

theorem isClosedEmbedding_incl : Topology.IsClosedEmbedding (incl (d := d)) :=
  continuous_incl.isClosedEmbedding injective_incl

/-! ## 3. The image is the complement of the affine chart -/

/-- The `(d+1)`-block of a point of `ℂP^{d+1}` whose `(0,0)` entry vanishes. -/
def deincl (y : CP (d + 1)) (hy : y.mat 0 0 = 0) : CP d := by
  refine ⟨Matrix.of fun i j => y.mat i.succ j.succ, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.conjTranspose_apply]
    simp only [Matrix.of_apply, Complex.star_def]
    exact y.prop.conj_entry j.succ i.succ
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hsplit := y.prop.sum_mul i.succ j.succ
    rw [Fin.sum_univ_succ, y.prop.col_eq_zero_of_diag_eq_zero hy i.succ, zero_mul,
      zero_add] at hsplit
    exact hsplit
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    have htr := y.prop.trace_eq
    simp only [Matrix.trace, Matrix.diag_apply] at htr
    rw [Fin.sum_univ_succ, hy, zero_add] at htr
    exact htr

@[simp] theorem deincl_mat (y : CP (d + 1)) (hy : y.mat 0 0 = 0) (i j : Fin (d + 1)) :
    (deincl y hy).mat i j = y.mat i.succ j.succ := rfl

theorem incl_deincl (y : CP (d + 1)) (hy : y.mat 0 0 = 0) : incl (deincl y hy) = y := by
  refine ext (Matrix.ext fun a b => ?_)
  refine Fin.cases ?_ ?_ a
  · rw [incl_mat, inclMat_zero_row]
    exact (y.prop.row_eq_zero_of_diag_eq_zero hy b).symm
  · intro i
    refine Fin.cases ?_ ?_ b
    · rw [incl_mat, inclMat_succ_zero]
      exact (y.prop.col_eq_zero_of_diag_eq_zero hy i.succ).symm
    · intro j
      rw [incl_mat, inclMat_succ_succ, deincl_mat]

/-- **The image of the hyperplane inclusion is exactly the complement of the affine
chart.** So `ℂP^{d+1}` is the disjoint union of the `2(d+1)`-cell `CP.chartSet (d+1)` and
the closed subspace `ℂP^d`. -/
theorem range_incl : Set.range (incl (d := d)) = {y : CP (d + 1) | y.mat 0 0 = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hy
    exact ⟨deincl y hy, incl_deincl y hy⟩

theorem chartSet_eq_compl_range_incl :
    chartSet (d + 1) = (Set.range (incl (d := d)))ᶜ := by
  rw [range_incl]
  rfl

theorem isClosed_range_incl : IsClosed (Set.range (incl (d := d))) :=
  isClosedEmbedding_incl.isClosed_range

end CP

end GroupApproximation.AlgTop
