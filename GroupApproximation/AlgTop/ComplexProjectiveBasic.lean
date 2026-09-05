import Mathlib

/-!
# `ℂP^d` as the space of rank-one projections

This file sets up the concrete model of complex projective space used by the LIX
campaign (Problem LIX of Schafhauser–Tikuisis–White): a *point* of `ℂP^d` **is** a
rank-one orthogonal projection in `M_{d+1}(ℂ)`,

```text
CP d = {q : Matrix (Fin (d+1)) (Fin (d+1)) ℂ // qᴴ = q ∧ q * q = q ∧ q.trace = 1}
```

carrying the subspace topology of the product topology on matrices. **No quotient
topology appears anywhere**, which is what makes every point-set statement below a
finite computation with matrix entries.

## Main results

The one nontrivial algebraic fact is the *rank-one normal form*, packaged here as the
vanishing of every `2 × 2` minor:

* `IsLineProj.minor` : `q a j * q j b = q j j * q a b`.

Its proof is elementary and self-contained. If `q j j ≠ 0`, the matrix
`colProj q j` with entries `q a j * q j b / q j j` is again a self-adjoint idempotent of
trace one satisfying `q * colProj q j = colProj q j * q = colProj q j`, so
`q - colProj q j` is a self-adjoint idempotent of trace `0`; and a self-adjoint
idempotent `r` has `trace r = ∑ a c, ‖r c a‖²`, so `trace r = 0` forces `r = 0`.
Neither the trace-equals-rank theorem nor the spectral theorem is used.

From the normal form everything else follows by computation:

* `IsLineProj.sum_normSq_eq_one`, `IsLineProj.norm_entry_le_one` — the entries are
  bounded by `1`, which gives `CompactSpace (CP d)`;
* `CP.ofVec` — a unit vector gives a point, whence `Nonempty (CP d)`;
* `CP.continuous_entry` — entry evaluation is continuous, the workhorse for every later
  continuity proof.

## Index convention

`CP d` is complex projective `d`-space: `CP 0` is a point and `CP d` is `2d`-dimensional
as a real manifold. This is the convention of the campaign manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` §2),
where `Y = ∏ⱼ ℂP^{dⱼ}` has `H^{2m}(Y;ℤ) ≅ ℤ` for `m = ∑ⱼ dⱼ`.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix Complex
open scoped ComplexConjugate

/-! ## 1. Self-adjoint idempotents -/

section SelfAdjointIdem

variable {n : Type*} [Fintype n] {q : Matrix n n ℂ}

/-- The `(a, b)` entry of a self-adjoint matrix is the conjugate of the `(b, a)` entry. -/
theorem conj_entry_of_herm (hh : qᴴ = q) (a b : n) : conj (q a b) = q b a := by
  have h1 := Matrix.ext_iff.2 hh b a
  rw [Matrix.conjTranspose_apply] at h1
  simpa only [Complex.star_def] using h1

/-- For a self-adjoint idempotent, the `j`-th diagonal entry is the squared norm of the
`j`-th column. In particular it is a nonnegative real number. -/
theorem diag_eq_sum_normSq (hh : qᴴ = q) (hi : q * q = q) (j : n) :
    q j j = ((∑ c, Complex.normSq (q c j) : ℝ) : ℂ) := by
  have h1 : q j j = ∑ c, q j c * q c j := by
    have h2 := Matrix.ext_iff.2 hi j j
    rw [Matrix.mul_apply] at h2
    exact h2.symm
  rw [h1, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.normSq_eq_conj_mul_self, conj_entry_of_herm hh c j]

/-- The trace of a self-adjoint idempotent is the sum of the squared norms of all its
entries. -/
theorem trace_eq_sum_normSq (hh : qᴴ = q) (hi : q * q = q) :
    q.trace = ((∑ j, ∑ c, Complex.normSq (q c j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => diag_eq_sum_normSq hh hi j

/-- A self-adjoint idempotent of trace zero is zero. This is the only positivity input of
the whole file. -/
theorem eq_zero_of_herm_idem_trace_zero (hh : qᴴ = q) (hi : q * q = q) (ht : q.trace = 0) :
    q = 0 := by
  have h1 : ((∑ j, ∑ c, Complex.normSq (q c j) : ℝ) : ℂ) = 0 := by
    rw [← trace_eq_sum_normSq hh hi]; exact ht
  have h2 : (∑ j, ∑ c, Complex.normSq (q c j)) = 0 := by exact_mod_cast h1
  have h3 : ∀ j ∈ (Finset.univ : Finset n), (0:ℝ) ≤ ∑ c, Complex.normSq (q c j) :=
    fun j _ => Finset.sum_nonneg fun c _ => Complex.normSq_nonneg _
  ext a b
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg h3).1 h2 b (Finset.mem_univ b)
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c (_ : c ∈ (Finset.univ : Finset n)) => Complex.normSq_nonneg (q c b))).1 h4 a
    (Finset.mem_univ a)
  simpa using Complex.normSq_eq_zero.1 h5

end SelfAdjointIdem

/-! ## 2. The defining predicate and the rank-one normal form -/

/-- `q` is a rank-one orthogonal projection: a self-adjoint idempotent of trace one. -/
def IsLineProj {n : Type*} [Fintype n] (q : Matrix n n ℂ) : Prop :=
  qᴴ = q ∧ q * q = q ∧ q.trace = 1

/-- The rank-one matrix built from the `j`-th column of `q`, normalized by `q j j`.
When `q` is a rank-one projection with `q j j ≠ 0`, this is `q` itself
(`IsLineProj.eq_colProj`). -/
def colProj {n : Type*} [Fintype n] (q : Matrix n n ℂ) (j : n) : Matrix n n ℂ :=
  Matrix.of fun x y => q x j * q j y / q j j

@[simp] theorem colProj_apply {n : Type*} [Fintype n] (q : Matrix n n ℂ) (j x y : n) :
    colProj q j x y = q x j * q j y / q j j := rfl

namespace IsLineProj

variable {n : Type*} [Fintype n] {q : Matrix n n ℂ}

theorem herm (h : IsLineProj q) : qᴴ = q := h.1
theorem idem (h : IsLineProj q) : q * q = q := h.2.1
theorem trace_eq (h : IsLineProj q) : q.trace = 1 := h.2.2

theorem conj_entry (h : IsLineProj q) (a b : n) : conj (q a b) = q b a :=
  conj_entry_of_herm h.herm a b

theorem diag_eq (h : IsLineProj q) (j : n) :
    q j j = ((∑ c, Complex.normSq (q c j) : ℝ) : ℂ) :=
  diag_eq_sum_normSq h.herm h.idem j

/-- The idempotent identity, read off entrywise. -/
theorem sum_mul (h : IsLineProj q) (x y : n) : (∑ c, q x c * q c y) = q x y := by
  have h2 := Matrix.ext_iff.2 h.idem x y
  rwa [Matrix.mul_apply] at h2

/-- The entries of a rank-one projection have total squared norm one. -/
theorem sum_normSq_eq_one (h : IsLineProj q) :
    (∑ j, ∑ c, Complex.normSq (q c j)) = 1 := by
  have h1 : ((∑ j, ∑ c, Complex.normSq (q c j) : ℝ) : ℂ) = 1 := by
    rw [← trace_eq_sum_normSq h.herm h.idem]; exact h.trace_eq
  exact_mod_cast h1

/-- Every entry of a rank-one projection has squared norm at most one. -/
theorem normSq_le_one (h : IsLineProj q) (a b : n) : Complex.normSq (q a b) ≤ 1 := by
  have hle : Complex.normSq (q a b) ≤ ∑ c, Complex.normSq (q c b) :=
    Finset.single_le_sum (f := fun c => Complex.normSq (q c b))
      (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have hle2 : (∑ c, Complex.normSq (q c b)) ≤ ∑ j, ∑ c, Complex.normSq (q c j) :=
    Finset.single_le_sum (f := fun j => ∑ c, Complex.normSq (q c j))
      (fun j _ => Finset.sum_nonneg fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
  calc Complex.normSq (q a b) ≤ ∑ c, Complex.normSq (q c b) := hle
    _ ≤ ∑ j, ∑ c, Complex.normSq (q c j) := hle2
    _ = 1 := h.sum_normSq_eq_one

/-- Every entry of a rank-one projection has norm at most one. -/
theorem norm_entry_le_one (h : IsLineProj q) (a b : n) : ‖q a b‖ ≤ 1 := by
  have h1 : ‖q a b‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact h.normSq_le_one a b
  nlinarith [norm_nonneg (q a b), h1]

/-- If a diagonal entry vanishes, so does the whole corresponding column. -/
theorem col_eq_zero_of_diag_eq_zero (h : IsLineProj q) {j : n} (hj : q j j = 0) (c : n) :
    q c j = 0 := by
  have h1 : ((∑ c, Complex.normSq (q c j) : ℝ) : ℂ) = 0 := by rw [← h.diag_eq j]; exact hj
  have h2 : (∑ c, Complex.normSq (q c j)) = 0 := by exact_mod_cast h1
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c (_ : c ∈ (Finset.univ : Finset n)) => Complex.normSq_nonneg (q c j))).1 h2 c
    (Finset.mem_univ c)
  exact Complex.normSq_eq_zero.1 h3

/-- **Rank-one normal form.** If `q j j ≠ 0` then `q` is recovered from its `j`-th column:
`q = colProj q j`. -/
theorem eq_colProj (h : IsLineProj q) {j : n} (ht : q j j ≠ 0) : q = colProj q j := by
  have hph : (colProj q j)ᴴ = colProj q j := by
    ext x y
    rw [Matrix.conjTranspose_apply, colProj_apply, colProj_apply]
    simp only [Complex.star_def, map_div₀, map_mul, h.conj_entry]
    ring
  have hqp : q * colProj q j = colProj q j := by
    ext x y
    rw [Matrix.mul_apply, colProj_apply]
    have hterm : ∀ c, q x c * colProj q j c y = (q x c * q c j) * (q j y / q j j) := by
      intro c; rw [colProj_apply]; ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_mul, h.sum_mul x j]
    ring
  have hpq : colProj q j * q = colProj q j := by
    ext x y
    rw [Matrix.mul_apply, colProj_apply]
    have hterm : ∀ c, colProj q j x c * q c y = (q x j / q j j) * (q j c * q c y) := by
      intro c; rw [colProj_apply]; ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, h.sum_mul j y]
    ring
  have hpp : colProj q j * colProj q j = colProj q j := by
    ext x y
    rw [Matrix.mul_apply, colProj_apply]
    have hterm : ∀ c, colProj q j x c * colProj q j c y
        = (q x j * q j y / (q j j * q j j)) * (q j c * q c j) := by
      intro c; rw [colProj_apply, colProj_apply]; field_simp; ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, h.sum_mul j j]
    field_simp
  have hpt : (colProj q j).trace = 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, colProj_apply]
    rw [← Finset.sum_div]
    have hs : (∑ x, q x j * q j x) = q j j := by
      have hjj := h.sum_mul j j
      rw [← hjj]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hs, div_self ht]
  have hr : q - colProj q j = 0 := by
    refine eq_zero_of_herm_idem_trace_zero ?_ ?_ ?_
    · rw [Matrix.conjTranspose_sub, h.herm, hph]
    · rw [sub_mul, mul_sub, mul_sub, h.idem, hqp, hpq, hpp]
      abel
    · rw [Matrix.trace_sub, h.trace_eq, hpt, sub_self]
  exact sub_eq_zero.1 hr

/-- **Rank-one normal form**, in the form of the vanishing of the `2 × 2` minors: for a
self-adjoint idempotent of trace one,
`q a j * q j b = q j j * q a b` for all indices. -/
theorem minor (h : IsLineProj q) (a b j : n) : q a j * q j b = q j j * q a b := by
  by_cases ht : q j j = 0
  · rw [h.col_eq_zero_of_diag_eq_zero ht a, ht, zero_mul, zero_mul]
  · have hq := Matrix.ext_iff.2 (h.eq_colProj ht) a b
    rw [colProj_apply] at hq
    rw [hq]
    field_simp

end IsLineProj

/-! ## 3. The space `CP d` -/

/-- **Complex projective `d`-space** as the space of rank-one orthogonal projections in
`M_{d+1}(ℂ)`, with the subspace topology. `CP 0` is a point. -/
def CP (d : ℕ) : Type :=
  {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ // IsLineProj q}

namespace CP

variable {d : ℕ}

instance : TopologicalSpace (CP d) :=
  inferInstanceAs (TopologicalSpace {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ // IsLineProj q})

instance : T2Space (CP d) :=
  inferInstanceAs (T2Space {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ // IsLineProj q})

/-- The underlying matrix of a point of `CP d`. -/
def mat (x : CP d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := x.1

theorem prop (x : CP d) : IsLineProj x.mat := x.2

theorem ext {x y : CP d} (h : x.mat = y.mat) : x = y := Subtype.ext h

theorem ext_iff {x y : CP d} : x = y ↔ ∀ a b, x.mat a b = y.mat a b :=
  ⟨fun h _ _ => by rw [h], fun h => ext (Matrix.ext h)⟩

/-- The inclusion of `CP d` into matrices is continuous. -/
theorem continuous_val : Continuous fun x : CP d => x.mat :=
  continuous_subtype_val

/-- Entry evaluation `CP d → ℂ` is continuous. -/
theorem continuous_entry (a b : Fin (d + 1)) : Continuous fun x : CP d => x.mat a b :=
  continuous_val.matrix_elem a b

/-- The subset of matrices cut out by the defining equations. -/
def carrier (d : ℕ) : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := {q | IsLineProj q}

theorem isClosed_carrier : IsClosed (carrier d) := by
  have htr : Continuous fun q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => q.trace := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i
  have h1 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | qᴴ = q} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have h2 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q * q = q} :=
    isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id
  have h3 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q.trace = 1} :=
    isClosed_eq htr continuous_const
  have hEq : carrier d = {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | qᴴ = q} ∩
      ({q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q * q = q} ∩
        {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q.trace = 1}) := rfl
  rw [hEq]
  exact h1.inter (h2.inter h3)

theorem isCompact_carrier : IsCompact (carrier d) := by
  have hsub : carrier d ⊆ (Metric.closedBall (0 : ℂ) 1).matrix := by
    intro q hq
    rw [Set.mem_matrix]
    intro a b
    have hq' : IsLineProj q := hq
    simpa only [Metric.mem_closedBall, dist_zero_right] using hq'.norm_entry_le_one a b
  exact IsCompact.of_isClosed_subset
    (IsCompact.matrix (m := Fin (d + 1)) (n := Fin (d + 1)) (isCompact_closedBall (0 : ℂ) 1))
    isClosed_carrier hsub

instance : CompactSpace (CP d) :=
  isCompact_iff_compactSpace.mp isCompact_carrier

/-! ### Points from unit vectors -/

/-- The outer product `v vᴴ` of a vector with itself is a rank-one projection as soon as
`v` has squared norm one. -/
theorem isLineProj_outer (v : Fin (d + 1) → ℂ) (hv : (∑ a, Complex.normSq (v a)) = 1) :
    IsLineProj (Matrix.of fun a b => v a * conj (v b)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, map_mul,
      Complex.conj_conj]
    ring
  · ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hterm : ∀ c, v a * conj (v c) * (v c * conj (v b))
        = (v a * conj (v b)) * ((Complex.normSq (v c) : ℝ) : ℂ) := by
      intro c
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← Complex.ofReal_sum, hv]
    simp
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    have hterm : ∀ a, v a * conj (v a) = ((Complex.normSq (v a) : ℝ) : ℂ) := by
      intro a; rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Complex.ofReal_sum, hv]
    norm_num

/-- The rank-one projection `v vᴴ` attached to a vector `v` of squared norm one. -/
def ofVec (v : Fin (d + 1) → ℂ) (hv : (∑ a, Complex.normSq (v a)) = 1) : CP d :=
  ⟨Matrix.of fun a b => v a * conj (v b), isLineProj_outer v hv⟩

@[simp] theorem ofVec_mat (v : Fin (d + 1) → ℂ) (hv : (∑ a, Complex.normSq (v a)) = 1)
    (a b : Fin (d + 1)) : (ofVec v hv).mat a b = v a * conj (v b) := rfl

/-- The base point `[1 : 0 : ⋯ : 0]`. -/
def basePoint (d : ℕ) : CP d :=
  ofVec (fun a => if a = 0 then 1 else 0) (by
    have hterm : ∀ a : Fin (d + 1),
        Complex.normSq (if a = 0 then (1:ℂ) else 0) = if a = 0 then (1:ℝ) else 0 := by
      intro a; by_cases ha : a = 0 <;> simp [ha]
    rw [Finset.sum_congr rfl fun a _ => hterm a]
    simp)

instance : Nonempty (CP d) := ⟨basePoint d⟩

end CP

end GroupApproximation.AlgTop
