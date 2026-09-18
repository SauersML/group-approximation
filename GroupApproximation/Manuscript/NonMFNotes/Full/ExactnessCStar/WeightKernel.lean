import GroupApproximation.Analysis.ExactnessPermanence
import Mathlib.Analysis.Real.Sqrt

/-!
# Square-root overlap kernels of property-A witnesses

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness" \cite{KWExact}.  In the Kirchberg--Wassermann / Ozawa argument a
system `a ↦ μ_a` of slowly varying finitely supported probability measures
(Yu's property A) is turned into the positive definite kernel
`k(a, b) = ∑_x √(μ_a x) √(μ_b x)`, whose Schur multiplier approximates the
identity on the translation operators of short length and kills the long
ones.  This file proves the kernel estimates.

* `window` --- the finite window `a · template` carrying `μ_a`;
* `sum_weight_eq_one`, `sum_weight_le_one`, `weight_le_one` --- mass bounds;
* `sqrtKernel` --- the overlap kernel `k(a, b)`;
* `sum_sq_sub_sqrt` --- `∑_x (√μ_a - √μ_b)² = 2 - 2 k(a, b)`;
* `sqrtKernel_nonneg`, `sqrtKernel_le_one`;
* `one_sub_sqrtKernel_le` --- `1 - k(a, b) ≤ ε / 2` when `a⁻¹ b ∈ R`;
* `diffSet`, `sqrtKernel_eq_zero` --- `k(a, b) = 0` unless `a⁻¹ b` lies in the
  finite difference set of the template.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.ExactnessPermanence

universe u

noncomputable section

section Kernel

variable {G : Type u} [Group G] {R : Finset G} {ε : ℝ}

local instance decEqWeightKernel : DecidableEq G := Classical.decEq G

/-- The window `a · template`, which carries the measure attached to `a`. -/
def window (W : PropertyAWitness G R ε) (a : G) : Finset G :=
  W.template.image fun s ↦ a * s

theorem mem_window_of_weight_ne_zero (W : PropertyAWitness G R ε) {a x : G}
    (hx : W.weight a x ≠ 0) : x ∈ window W a := by
  have hmem : a⁻¹ * x ∈ W.template := by
    by_contra hnot
    exact hx (W.weight_eq_zero a x hnot)
  exact Finset.mem_image.mpr ⟨a⁻¹ * x, hmem, mul_inv_cancel_left a x⟩

theorem weight_eq_zero_of_not_mem_window (W : PropertyAWitness G R ε) {a x : G}
    (hx : x ∉ window W a) : W.weight a x = 0 := by
  by_contra h
  exact hx (mem_window_of_weight_ne_zero W h)

theorem mem_union_window_left (W : PropertyAWitness G R ε) {a x : G} (b : G)
    (hx : W.weight a x ≠ 0) : x ∈ window W a ∪ window W b :=
  Finset.mem_union_left (window W b) (mem_window_of_weight_ne_zero W hx)

theorem mem_union_window_right (W : PropertyAWitness G R ε) (a : G) {b x : G}
    (hx : W.weight b x ≠ 0) : x ∈ window W a ∪ window W b :=
  Finset.mem_union_right (window W a) (mem_window_of_weight_ne_zero W hx)

/-- The measure attached to `a` has total mass one on its window. -/
theorem sum_window_weight (W : PropertyAWitness G R ε) (a : G) :
    ∑ x ∈ window W a, W.weight a x = 1 := by
  have hinj : Set.InjOn (fun s ↦ a * s) (W.template : Set G) := by
    intro s _ t _ hst
    exact mul_left_cancel hst
  rw [window, Finset.sum_image hinj]
  exact W.weight_sum a

/-- The measure attached to `a` has total mass one on any finite set containing
its support. -/
theorem sum_weight_eq_one (W : PropertyAWitness G R ε) (a : G) {T : Finset G}
    (hT : ∀ x, W.weight a x ≠ 0 → x ∈ T) : ∑ x ∈ T, W.weight a x = 1 := by
  have h1 : ∑ x ∈ T, W.weight a x = ∑ x ∈ T ∪ window W a, W.weight a x :=
    Finset.sum_subset Finset.subset_union_left fun x _ hx ↦ by
      by_contra h
      exact hx (hT x h)
  have h2 : ∑ x ∈ window W a, W.weight a x = ∑ x ∈ T ∪ window W a, W.weight a x :=
    Finset.sum_subset Finset.subset_union_right fun _ _ hx ↦
      weight_eq_zero_of_not_mem_window W hx
  rw [h1, ← h2, sum_window_weight]

/-- Every partial sum of a measure is at most one. -/
theorem sum_weight_le_one (W : PropertyAWitness G R ε) (a : G) (S : Finset G) :
    ∑ x ∈ S, W.weight a x ≤ 1 := by
  calc ∑ x ∈ S, W.weight a x ≤ ∑ x ∈ S ∪ window W a, W.weight a x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          fun x _ _ ↦ W.weight_nonneg a x
    _ = 1 := sum_weight_eq_one W a fun _ hx ↦
        Finset.mem_union_right S (mem_window_of_weight_ne_zero W hx)

theorem weight_le_one (W : PropertyAWitness G R ε) (a x : G) : W.weight a x ≤ 1 := by
  have h := sum_weight_le_one W a {x}
  rwa [Finset.sum_singleton] at h

/-- The square-root overlap kernel `k(a, b) = ∑_x √(μ_a x) √(μ_b x)`. -/
def sqrtKernel (W : PropertyAWitness G R ε) (a b : G) : ℝ :=
  ∑ x ∈ window W a, Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x)

/-- The overlap kernel may be summed over any finite set containing the support
of `μ_a`. -/
theorem sqrtKernel_eq_sum (W : PropertyAWitness G R ε) (a b : G) {T : Finset G}
    (hT : ∀ x, W.weight a x ≠ 0 → x ∈ T) :
    sqrtKernel W a b
      = ∑ x ∈ T, Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x) := by
  have hz : ∀ x, W.weight a x = 0 →
      Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x) = 0 := by
    intro x hx
    rw [hx, Real.sqrt_zero, zero_mul]
  have h1 : ∑ x ∈ window W a, Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x)
      = ∑ x ∈ T ∪ window W a, Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x) :=
    Finset.sum_subset Finset.subset_union_right fun x _ hx ↦
      hz x (weight_eq_zero_of_not_mem_window W hx)
  have h2 : ∑ x ∈ T, Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x)
      = ∑ x ∈ T ∪ window W a, Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x) :=
    Finset.sum_subset Finset.subset_union_left fun x _ hx ↦ hz x (by
      by_contra h
      exact hx (hT x h))
  unfold sqrtKernel
  rw [h1, h2]

/-- `(√s - √t)² ≤ |s - t|` for nonnegative reals. -/
theorem sq_sub_sqrt_le_abs {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (Real.sqrt s - Real.sqrt t) ^ 2 ≤ |s - t| := by
  have hfac : s - t = (Real.sqrt s - Real.sqrt t) * (Real.sqrt s + Real.sqrt t) := by
    linear_combination (-1 : ℝ) * Real.sq_sqrt hs + Real.sq_sqrt ht
  have hsum : |Real.sqrt s - Real.sqrt t| ≤ Real.sqrt s + Real.sqrt t :=
    abs_le.mpr ⟨by linarith [Real.sqrt_nonneg s, Real.sqrt_nonneg t],
      by linarith [Real.sqrt_nonneg s, Real.sqrt_nonneg t]⟩
  rw [hfac, abs_mul,
    abs_of_nonneg (add_nonneg (Real.sqrt_nonneg s) (Real.sqrt_nonneg t)), ← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- **The overlap identity**: `∑_x (√μ_a x - √μ_b x)² = 2 - 2 k(a, b)`. -/
theorem sum_sq_sub_sqrt (W : PropertyAWitness G R ε) (a b : G) :
    ∑ x ∈ window W a ∪ window W b,
        (Real.sqrt (W.weight a x) - Real.sqrt (W.weight b x)) ^ 2
      = 2 - 2 * sqrtKernel W a b := by
  have hterm : ∀ x, (Real.sqrt (W.weight a x) - Real.sqrt (W.weight b x)) ^ 2
      = W.weight a x + W.weight b x
        - 2 * (Real.sqrt (W.weight a x) * Real.sqrt (W.weight b x)) := by
    intro x
    linear_combination Real.sq_sqrt (W.weight_nonneg a x)
      + Real.sq_sqrt (W.weight_nonneg b x)
  simp only [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_weight_eq_one W a (fun _ hx ↦ mem_union_window_left W b hx),
    sum_weight_eq_one W b (fun _ hx ↦ mem_union_window_right W a hx),
    ← sqrtKernel_eq_sum W a b (fun _ hx ↦ mem_union_window_left W b hx)]
  ring

theorem sqrtKernel_nonneg (W : PropertyAWitness G R ε) (a b : G) :
    0 ≤ sqrtKernel W a b := by
  unfold sqrtKernel
  exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem sqrtKernel_le_one (W : PropertyAWitness G R ε) (a b : G) :
    sqrtKernel W a b ≤ 1 := by
  have h := sum_sq_sub_sqrt W a b
  have hnn : 0 ≤ ∑ x ∈ window W a ∪ window W b,
      (Real.sqrt (W.weight a x) - Real.sqrt (W.weight b x)) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  linarith

/-- **Short translations**: if `a⁻¹ b ∈ R` then `1 - k(a, b) ≤ ε / 2`. -/
theorem one_sub_sqrtKernel_le (W : PropertyAWitness G R ε) {a b : G}
    (hab : a⁻¹ * b ∈ R) : 1 - sqrtKernel W a b ≤ ε / 2 := by
  have h := sum_sq_sub_sqrt W a b
  have hle : ∑ x ∈ window W a ∪ window W b,
        (Real.sqrt (W.weight a x) - Real.sqrt (W.weight b x)) ^ 2
      ≤ ∑ x ∈ window W a ∪ window W b, |W.weight a x - W.weight b x| :=
    Finset.sum_le_sum fun x _ ↦
      sq_sub_sqrt_le_abs (W.weight_nonneg a x) (W.weight_nonneg b x)
  have hclose := W.weight_close a b hab (window W a ∪ window W b)
    (fun _ hx ↦ mem_union_window_left W b hx) (fun _ hx ↦ mem_union_window_right W a hx)
  linarith

/-- The finite difference set `template · template⁻¹`. -/
def diffSet (W : PropertyAWitness G R ε) : Finset G :=
  (W.template ×ˢ W.template).image fun p ↦ p.1 * p.2⁻¹

/-- **Long translations**: `k(a, b) = 0` unless `a⁻¹ b` lies in the difference
set of the template. -/
theorem sqrtKernel_eq_zero (W : PropertyAWitness G R ε) {a b : G}
    (hab : a⁻¹ * b ∉ diffSet W) : sqrtKernel W a b = 0 := by
  unfold sqrtKernel
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  by_contra hne
  have ha : W.weight a x ≠ 0 := fun h0 ↦ hne (by rw [h0, Real.sqrt_zero, zero_mul])
  have hb : W.weight b x ≠ 0 := fun h0 ↦ hne (by rw [h0, Real.sqrt_zero, mul_zero])
  have ha' : a⁻¹ * x ∈ W.template := by
    by_contra h
    exact ha (W.weight_eq_zero a x h)
  have hb' : b⁻¹ * x ∈ W.template := by
    by_contra h
    exact hb (W.weight_eq_zero b x h)
  refine hab (Finset.mem_image.mpr
    ⟨(a⁻¹ * x, b⁻¹ * x), Finset.mem_product.mpr ⟨ha', hb'⟩, ?_⟩)
  show (a⁻¹ * x) * (b⁻¹ * x)⁻¹ = a⁻¹ * b
  rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

end Kernel

end

end GroupApproximation.Full.NN09c
