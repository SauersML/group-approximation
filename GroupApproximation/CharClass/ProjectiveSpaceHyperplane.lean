-- Re-proved in the `GroupApproximation.CharClass` namespace from the paused fleet's
-- `GroupApproximation/AlgTop/ComplexProjectiveHyperplane.lean`, which is red at the pin and owned by no
-- lane of the LIX program.  Lane `cc-projective` owns this copy.
import GroupApproximation.CharClass.ProjectiveSpaceChart

/-!
# The hyperplane `ℂP^d ⊂ ℂP^{d+1}`

The linear hyperplane `z₀ = 0` inside `ℂ^{d+2}` gives a copy of `ℂP^d` inside `ℂP^{d+1}`.
In the projection model this is the map that pads a rank-one projection by a zero row and
a zero column:

```text
incl x = ⎛ 0  0 ⎞
         ⎝ 0  x ⎠.
```

## Main results

* `CPn.incl : CP d → CP (d+1)` and its entries;
* `CPn.isClosedEmbedding_incl` — it is a closed topological embedding (continuous and
  injective out of a compact space into a Hausdorff space);
* `CPn.range_incl : Set.range incl = {y | entry y 0 0 = 0}` — the image is exactly the
  complement of the affine chart `CPn.chartSet (d+1)`;
* `CPn.chartSet_eq_compl_range_incl` — the chart and the hyperplane partition `ℂP^{d+1}`.

Together with `GroupApproximation/AlgTop/ComplexProjectiveChart.lean` this is the cell
decomposition step: `ℂP^{d+1}` is `ℂP^d` with one open `2(d+1)`-cell attached, the cell
being the affine chart `ℂ^{d+1}`. Iterating gives the filtration
`ℂP^0 ⊂ ℂP^1 ⊂ ⋯ ⊂ ℂP^n` with exactly one cell in each even dimension `0, 2, …, 2n` and
none in odd dimensions; since all cells are even-dimensional, every cellular boundary map
of `ℂP^n` vanishes.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Matrix
open GroupApproximation.STW59

namespace CPn

variable {d : ℕ}

/-! ## 1. The padded matrix -/

/-- The matrix of `x : CP d` padded by a zero row and a zero column. -/
def inclMat (x : CP d) : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ :=
  Matrix.of (Fin.cons (0 : Fin (d + 2) → ℂ)
    fun i => Fin.cons (0 : ℂ) ((x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i))

@[simp] theorem inclMat_zero_row (x : CP d) (b : Fin (d + 2)) : inclMat x 0 b = 0 := by
  simp [inclMat]

@[simp] theorem inclMat_succ_zero (x : CP d) (i : Fin (d + 1)) : inclMat x i.succ 0 = 0 := by
  simp [inclMat]

@[simp] theorem inclMat_succ_succ (x : CP d) (i j : Fin (d + 1)) :
    inclMat x i.succ j.succ = entry x i j := by
  simp [inclMat]

@[simp] theorem inclMat_zero_col (x : CP d) (a : Fin (d + 2)) : inclMat x a 0 = 0 := by
  refine Fin.cases ?_ ?_ a <;> simp

theorem inclMat_mem (x : CP d) : inclMat x ∈ cpSet (d + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · refine Matrix.ext fun a b => ?_
    rw [Matrix.conjTranspose_apply]
    refine Fin.cases ?_ ?_ a
    · refine Fin.cases ?_ ?_ b <;> intros <;> simp
    · intro i
      refine Fin.cases ?_ ?_ b
      · simp
      · intro j
        rw [inclMat_succ_succ, inclMat_succ_succ]
        exact (entry_symm x i j).symm
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
        exact entry_sum_mul x i j
  · simp only [Matrix.trace, Matrix.diag_apply]
    rw [Fin.sum_univ_succ]
    simp only [inclMat_zero_row, inclMat_succ_succ, zero_add]
    have h := trace_coe x
    simpa only [Matrix.trace, Matrix.diag_apply] using h

/-- **The hyperplane inclusion** `ℂP^d ↪ ℂP^{d+1}`,
`[z₀ : ⋯ : z_d] ↦ [0 : z₀ : ⋯ : z_d]`. -/
def incl (x : CP d) : CP (d + 1) := ⟨inclMat x, inclMat_mem x⟩

@[simp] theorem incl_entry (x : CP d) (a b : Fin (d + 2)) :
    entry (incl x) a b = inclMat x a b := rfl

@[simp] theorem incl_entry_zero_zero (x : CP d) : entry (incl x) 0 0 = 0 := by simp

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
      simpa only [inclMat_succ_succ] using continuous_entry (d := d) i j

theorem injective_incl : Function.Injective (incl (d := d)) := by
  intro x y hxy
  refine ext fun i j => ?_
  have h : entry (incl x) i.succ j.succ = entry (incl y) i.succ j.succ := by rw [hxy]
  simpa only [incl_entry, inclMat_succ_succ] using h

theorem isClosedEmbedding_incl : Topology.IsClosedEmbedding (incl (d := d)) :=
  continuous_incl.isClosedEmbedding injective_incl

theorem isClosed_range_incl : IsClosed (Set.range (incl (d := d))) :=
  isClosedEmbedding_incl.isClosed_range

/-! ## 3. The image is the complement of the affine chart -/

/-- The `(d+1)`-block of a point of `ℂP^{d+1}` whose `(0,0)` entry vanishes. -/
def deincl (y : CP (d + 1)) (hy : entry y 0 0 = 0) : CP d := by
  refine ⟨Matrix.of fun i j => entry y i.succ j.succ, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.conjTranspose_apply]
    simp only [Matrix.of_apply]
    exact (entry_symm y i.succ j.succ).symm
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hsplit := entry_sum_mul y i.succ j.succ
    rw [Fin.sum_univ_succ, entry_col_eq_zero y hy i.succ, zero_mul, zero_add] at hsplit
    exact hsplit
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    have htr := trace_coe y
    simp only [Matrix.trace, Matrix.diag_apply] at htr
    rw [Fin.sum_univ_succ] at htr
    rw [show ((y : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) 0 0) = entry y 0 0 from rfl, hy,
      zero_add] at htr
    exact htr

@[simp] theorem deincl_entry (y : CP (d + 1)) (hy : entry y 0 0 = 0) (i j : Fin (d + 1)) :
    entry (deincl y hy) i j = entry y i.succ j.succ := rfl

theorem incl_deincl (y : CP (d + 1)) (hy : entry y 0 0 = 0) : incl (deincl y hy) = y := by
  refine ext fun a b => ?_
  refine Fin.cases ?_ ?_ a
  · rw [incl_entry, inclMat_zero_row]
    exact (entry_row_eq_zero y hy b).symm
  · intro i
    refine Fin.cases ?_ ?_ b
    · rw [incl_entry, inclMat_succ_zero]
      exact (entry_col_eq_zero y hy i.succ).symm
    · intro j
      rw [incl_entry, inclMat_succ_succ, deincl_entry]

/-- **The image of the hyperplane inclusion is exactly the complement of the affine
chart.** So `ℂP^{d+1}` is the disjoint union of the open `2(d+1)`-cell
`CPn.chartSet (d+1)` and the closed subspace `ℂP^d`. -/
theorem range_incl : Set.range (incl (d := d)) = {y : CP (d + 1) | entry y 0 0 = 0} := by
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

/-- The base point of `ℂP^{d+1}` is not in the hyperplane. -/
theorem basePoint_notMem_range_incl : basePoint (d + 1) ∉ Set.range (incl (d := d)) := by
  rw [range_incl]
  intro h
  have h1 : entry (basePoint (d + 1)) 0 0 = 0 := h
  rw [basePoint_entry_zero_zero] at h1
  exact one_ne_zero h1

end CPn

end GroupApproximation.CharClass
