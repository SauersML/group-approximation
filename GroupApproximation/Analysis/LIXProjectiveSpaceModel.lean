import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A concrete matrix model of complex projective space

This file supplies the geometric base spaces for the STW Problem LIX counterexample
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`)
**without any vector-bundle library**.

Complex projective space is modelled as a space of matrices:

`CP d := {q : Matrix (Fin (d+1)) (Fin (d+1)) ℂ // qᴴ = q ∧ q * q = q ∧ q.trace = 1}`

carrying the subspace topology of the product topology on
`Matrix (Fin (d+1)) (Fin (d+1)) ℂ` (`Mathlib/Topology/Instances/Matrix.lean`; no norm is
required, and none of Mathlib's *non-instance* matrix norms is opened here).  This is a
model of `ℂP^d`: a point of `ℂP^d` is a complex line in `ℂ^{d+1}`, and a line is the same
thing as the orthogonal projection onto it, i.e. a self-adjoint idempotent of trace one.

The decisive advantage for formalization is that the **tautological line bundle's
projection is literally `Subtype.val`** (`STW59.taut`, `STW59.tautMat` below): a
continuous projection-valued matrix function on the base, with no quotient topology and
no bundle theory.  All the `c₁` data downstream is carried by honest matrix-valued
functions.

## Conventions shared with the rest of the LIX lanes

* A *bundle* is a projection `p : Matrix ι ι C(X, ℂ)`, exactly as in
  `GroupApproximation/KTheory/MatrixProjection.lean`; *bundle isomorphism* is
  `GroupApproximation.MurrayVonNeumannEquiv` from
  `GroupApproximation/Analysis/FiniteCStarMurrayVonNeumann.lean`.  Neither notion is
  redefined here.
* `STW59.matEval x : Matrix ι κ C(X, ℂ) → Matrix ι κ ℂ` is evaluation at a point of the
  base; it is the bridge between the "matrix over the function algebra" picture and the
  pointwise linear algebra, and it is multiplicative and `star`-preserving
  (`STW59.matEval_mul`, `STW59.matEval_conjTranspose`).
* Vectors are plain functions `n → ℂ`, **not** `EuclideanSpace ℂ n`; the unit sphere is
  `STW59.unitVectors n`, cut out by `∑ i, ‖x i‖ ^ 2 = 1`.  This avoids `PiLp` entirely.
* `CP d` uses matrices of size `d + 1`, i.e. `CP d` models `ℂP^d`.
* Projections are Mathlib's `IsStarProjection`; no new predicate is introduced.  For a
  square complex matrix `star q = qᴴ`, so `IsStarProjection q` is exactly
  `qᴴ = q ∧ q * q = q` (`STW59.isStarProjection_matrix_iff`).

## Main results

* `STW59.isCompact_cpSet`, `STW59.CP.instCompactSpace`, `STW59.CP.instNonempty` — the
  model is a nonempty compact Hausdorff space (Hausdorffness is the ambient
  `T2Space (Matrix m n ℂ)` instance, inherited by the subtype).
* `STW59.eq_rankOneProj_of_trace_one` — a trace-one projection *is* `x xᴴ` for a unit
  vector `x`; this is the "rank one" content, proved elementarily.  The route replaces
  the spectral theorem by `STW59.proj_eq_zero_of_trace_eq_zero`: a projection whose
  trace vanishes is zero, because its trace is the total squared norm of its entries.
* `STW59.cpSet_eq_image` — `ℂP^d` is exactly the image of the unit sphere of `ℂ^{d+1}`
  under the continuous map `x ↦ x xᴴ`.
* `STW59.exists_natCast_trace` — **the trace of a projection is a natural number**,
  namely its rank.  Also proved without the spectral theorem, by peeling off rank-one
  subprojections (`STW59.exists_rankOneProj_absorbed`).
* `STW59.isStarProjection_tautMat`, `STW59.trace_tautMat` — the tautological line is a
  rank-one projection in `Matrix (Fin (d+1)) (Fin (d+1)) C(CP d, ℂ)`.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix

noncomputable section

/-! ### Two scalar identities -/

/-- `star z * z` is the (real) squared modulus of `z`. -/
theorem star_mul_self_eq_normSq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.normSq_eq_conj_mul_self.symm

/-- `z * star z` is the (real) squared modulus of `z`. -/
theorem mul_star_self_eq_normSq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]; exact star_mul_self_eq_normSq z

/-! ### Matrix projections over an arbitrary `*`-ring -/

section GeneralProj

variable {m A : Type*} [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]

theorem conjTranspose_eq_of_isStarProjection {q : Matrix m m A} (hq : IsStarProjection q) :
    qᴴ = q := by
  rw [← Matrix.star_eq_conjTranspose]
  exact hq.isSelfAdjoint.star_eq

theorem isStarProjection_matrix_iff {q : Matrix m m A} :
    IsStarProjection q ↔ qᴴ = q ∧ q * q = q := by
  rw [isStarProjection_iff']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← Matrix.star_eq_conjTranspose]; exact h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by rw [Matrix.star_eq_conjTranspose]; exact h1⟩

end GeneralProj

/-! ### Projections over `ℂ`, entrywise -/

section Entrywise

variable {n : Type*} [Fintype n] {q : Matrix n n ℂ}

/-- The entries of a projection are conjugate-symmetric. -/
theorem proj_entry_symm (hq : IsStarProjection q) (i j : n) : q i j = star (q j i) := by
  have h := congrFun (congrFun (conjTranspose_eq_of_isStarProjection hq) i) j
  rw [Matrix.conjTranspose_apply] at h
  exact h.symm

/-- Every diagonal entry of a projection is the squared norm of its column.  In
particular it is a nonnegative real number. -/
theorem proj_diag_eq (hq : IsStarProjection q) (j : n) :
    q j j = ((∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : (q * q) j j = ∑ k, q j k * q k j := Matrix.mul_apply
  rw [hq.isIdempotentElem.eq] at h1
  rw [h1, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [proj_entry_symm hq j k]
  exact star_mul_self_eq_normSq (q k j)

/-- The trace of a projection is the total squared norm of its entries. -/
theorem proj_trace_eq (hq : IsStarProjection q) :
    q.trace = ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) := by
  have hd : q.trace = ∑ j, q j j := rfl
  rw [hd, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => proj_diag_eq hq j

theorem proj_column_nonneg (q : Matrix n n ℂ) (j : n) :
    (0 : ℝ) ≤ ∑ k, ‖q k j‖ ^ 2 :=
  Finset.sum_nonneg fun k _ => by positivity

theorem proj_sq_le_column (q : Matrix n n ℂ) (i j : n) :
    ‖q i j‖ ^ 2 ≤ ∑ k, ‖q k j‖ ^ 2 :=
  Finset.single_le_sum (f := fun k => ‖q k j‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)

theorem proj_column_le_total (q : Matrix n n ℂ) (j : n) :
    (∑ k, ‖q k j‖ ^ 2) ≤ ∑ j', ∑ k, ‖q k j'‖ ^ 2 :=
  Finset.single_le_sum (f := fun j' => ∑ k, ‖q k j'‖ ^ 2)
    (fun j' _ => proj_column_nonneg q j') (Finset.mem_univ j)

/-- **A projection with vanishing trace is zero.**  This is the elementary substitute
for the spectral theorem used throughout this file. -/
theorem proj_eq_zero_of_trace_eq_zero (hq : IsStarProjection q) (h : q.trace = 0) :
    q = 0 := by
  have h1 : ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    rw [← proj_trace_eq hq, h, Complex.ofReal_zero]
  have h2 : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1
  ext i j
  have h3 : (∑ k, ‖q k j‖ ^ 2) ≤ 0 := by
    have := proj_column_le_total q j
    linarith
  have h4 : ‖q i j‖ ^ 2 ≤ 0 := le_trans (proj_sq_le_column q i j) h3
  have h5 : ‖q i j‖ = 0 := by nlinarith [norm_nonneg (q i j)]
  simpa using h5

/-- A nonzero matrix has a column of nonzero norm.  (No projection hypothesis is
needed; the entrywise bound `proj_sq_le_column` holds for every matrix.) -/
theorem exists_column_ne_zero (hne : q ≠ 0) :
    ∃ j : n, (∑ k, ‖q k j‖ ^ 2) ≠ 0 := by
  by_contra hcon
  apply hne
  ext i j
  have hzero : (∑ k, ‖q k j‖ ^ 2) = 0 := by
    by_contra hj
    exact hcon ⟨j, hj⟩
  have h4 : ‖q i j‖ ^ 2 ≤ 0 := by
    have := proj_sq_le_column q i j
    linarith
  have h5 : ‖q i j‖ = 0 := by nlinarith [norm_nonneg (q i j)]
  simpa using h5

/-- The total squared norm of the entries of a trace-one projection is one. -/
theorem proj_sum_sq_eq_one (hq : IsStarProjection q) (ht : q.trace = 1) :
    (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 1 := by
  have h1 : ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [← proj_trace_eq hq, ht, Complex.ofReal_one]
  exact_mod_cast h1

/-- Every entry of a trace-one projection has norm at most one; this is the boundedness
that makes the model of `ℂP^d` compact. -/
theorem proj_norm_entry_le_one (hq : IsStarProjection q) (ht : q.trace = 1) (i j : n) :
    ‖q i j‖ ≤ 1 := by
  have h1 : (∑ k, ‖q k j‖ ^ 2) ≤ 1 := by
    have hle := proj_column_le_total q j
    have := proj_sum_sq_eq_one hq ht
    linarith
  have h2 : ‖q i j‖ ^ 2 ≤ 1 := le_trans (proj_sq_le_column q i j) h1
  nlinarith [norm_nonneg (q i j)]

/-- The difference of two projections, one absorbed by the other, is a projection. -/
theorem isStarProjection_sub {P : Matrix n n ℂ} (hq : IsStarProjection q)
    (hP : IsStarProjection P) (h1 : q * P = P) (h2 : P * q = P) :
    IsStarProjection (q - P) := by
  rw [isStarProjection_matrix_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_sub, conjTranspose_eq_of_isStarProjection hq,
      conjTranspose_eq_of_isStarProjection hP]
  · have hexp : (q - P) * (q - P) = q * q - q * P - P * q + P * P := by noncomm_ring
    rw [hexp, hq.isIdempotentElem.eq, hP.isIdempotentElem.eq, h1, h2]
    abel

end Entrywise

/-! ### Unit vectors and rank-one projections -/

/-- The unit sphere of `ℂ^n`, as a subset of the product space `n → ℂ`.

Model choice: vectors are plain functions, so no `PiLp`/`EuclideanSpace` instance is
involved anywhere in this development. -/
def unitVectors (n : Type*) [Fintype n] : Set (n → ℂ) := {x | ∑ i, ‖x i‖ ^ 2 = 1}

theorem mem_unitVectors_iff {n : Type*} [Fintype n] {x : n → ℂ} :
    x ∈ unitVectors n ↔ ∑ i, ‖x i‖ ^ 2 = 1 := Iff.rfl

/-- For `x` a unit vector, `∑ k, star (x k) * x k = 1` in `ℂ`. -/
theorem sum_star_mul_self {n : Type*} [Fintype n] {x : n → ℂ} (hx : x ∈ unitVectors n) :
    ∑ k, star (x k) * x k = 1 := by
  have h : ∑ k, star (x k) * x k = ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => star_mul_self_eq_normSq (x k)
  rw [h, mem_unitVectors_iff.mp hx, Complex.ofReal_one]

/-- The rank-one matrix `x xᴴ`. -/
def rankOneProj {n : Type*} (x : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec x (star x)

@[simp]
theorem rankOneProj_apply {n : Type*} (x : n → ℂ) (i j : n) :
    rankOneProj x i j = x i * star (x j) := rfl

theorem isStarProjection_rankOneProj {n : Type*} [Fintype n] {x : n → ℂ}
    (hx : x ∈ unitVectors n) : IsStarProjection (rankOneProj x) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · ext i j
    rw [Matrix.conjTranspose_apply, rankOneProj_apply, rankOneProj_apply, star_mul,
      star_star, mul_comm]
  · ext i j
    rw [Matrix.mul_apply]
    have hre : ∀ k, rankOneProj x i k * rankOneProj x k j
        = (x i * star (x j)) * (star (x k) * x k) := by
      intro k
      rw [rankOneProj_apply, rankOneProj_apply]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hre k), ← Finset.mul_sum, sum_star_mul_self hx,
      mul_one, rankOneProj_apply]

theorem trace_rankOneProj {n : Type*} [Fintype n] {x : n → ℂ} (hx : x ∈ unitVectors n) :
    (rankOneProj x).trace = 1 := by
  have hd : (rankOneProj x).trace = ∑ i, rankOneProj x i i := rfl
  have h : ∀ i, rankOneProj x i i = star (x i) * x i := by
    intro i; rw [rankOneProj_apply, mul_comm]
  rw [hd, Finset.sum_congr rfl (fun i _ => h i), sum_star_mul_self hx]

theorem continuous_rankOneProj (n : Type*) [Fintype n] :
    Continuous (rankOneProj : (n → ℂ) → _) := by
  refine continuous_matrix fun i j => ?_
  simp only [rankOneProj_apply]
  exact (continuous_apply i).mul ((continuous_apply j).star)

theorem isClosed_unitVectors (n : Type*) [Fintype n] : IsClosed (unitVectors n) := by
  have hcont : Continuous fun x : n → ℂ => ∑ i, ‖x i‖ ^ 2 :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).norm).pow 2
  simpa [unitVectors] using isClosed_eq hcont continuous_const

theorem isCompact_unitVectors (n : Type*) [Fintype n] : IsCompact (unitVectors n) := by
  have hball : IsCompact (Set.univ.pi fun _ : n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hball.of_isClosed_subset (isClosed_unitVectors n) ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Metric.mem_closedBall,
    dist_zero_right]
  intro i
  have hsum : ∑ i, ‖x i‖ ^ 2 = 1 := hx
  have h2 : ‖x i‖ ^ 2 ≤ 1 := by
    have hle : ‖x i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ i)
    linarith
  nlinarith [norm_nonneg (x i)]

/-! ### Peeling a rank-one subprojection off a projection -/

/-- If a unit vector `x` is fixed by the projection `q`, then `q` absorbs the rank-one
projection `x xᴴ` on both sides. -/
theorem rankOneProj_absorbed {n : Type*} [Fintype n] {q : Matrix n n ℂ}
    (hq : IsStarProjection q) {x : n → ℂ} (hx : x ∈ unitVectors n)
    (hfix : ∀ i, (∑ k, q i k * x k) = x i) :
    q * rankOneProj x = rankOneProj x ∧ rankOneProj x * q = rankOneProj x := by
  have hPproj : IsStarProjection (rankOneProj x) := isStarProjection_rankOneProj hx
  have hqP : q * rankOneProj x = rankOneProj x := by
    ext i i'
    rw [Matrix.mul_apply]
    have hre : ∀ k, q i k * rankOneProj x k i' = (q i k * x k) * star (x i') := by
      intro k; rw [rankOneProj_apply]; ring
    rw [Finset.sum_congr rfl (fun k _ => hre k), ← Finset.sum_mul, hfix i, rankOneProj_apply]
  refine ⟨hqP, ?_⟩
  have h1 : (q * rankOneProj x)ᴴ = (rankOneProj x)ᴴ := congrArg _ hqP
  rw [Matrix.conjTranspose_mul, conjTranspose_eq_of_isStarProjection hPproj,
    conjTranspose_eq_of_isStarProjection hq] at h1
  exact h1

/-- **Normalizing a column of a projection produces an absorbed rank-one
subprojection.**  If the `j`-th column of the projection `q` has nonzero norm, then
`x = q(·,j)/‖q(·,j)‖` is a unit vector and `P = x xᴴ` satisfies `q P = P` and `P q = P`.

The proof is elementary: the column of a projection is a fixed vector of it. -/
theorem exists_rankOneProj_absorbed {n : Type*} [Fintype n] {q : Matrix n n ℂ}
    (hq : IsStarProjection q) {j : n} (hj : (∑ k, ‖q k j‖ ^ 2) ≠ 0) :
    ∃ x ∈ unitVectors n, q * rankOneProj x = rankOneProj x ∧
      rankOneProj x * q = rankOneProj x := by
  have hjpos : 0 < ∑ k, ‖q k j‖ ^ 2 :=
    lt_of_le_of_ne (proj_column_nonneg q j) (Ne.symm hj)
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = ∑ k, ‖q k j‖ ^ 2 :=
    ⟨Real.sqrt (∑ k, ‖q k j‖ ^ 2), Real.sqrt_pos.mpr hjpos, Real.sq_sqrt hjpos.le⟩
  have hnorms : ‖((s : ℝ) : ℂ)‖ = s := Complex.norm_of_nonneg hs0.le
  have hx : (fun i => q i j / ((s : ℝ) : ℂ)) ∈ unitVectors n := by
    show (∑ i, ‖q i j / ((s : ℝ) : ℂ)‖ ^ 2) = 1
    have hterm : ∀ i : n, ‖q i j / ((s : ℝ) : ℂ)‖ ^ 2 = ‖q i j‖ ^ 2 / s ^ 2 := by
      intro i
      rw [norm_div, hnorms, div_pow]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div, hs2, div_self hj]
  have hfix : ∀ i, (∑ k, q i k * (q k j / ((s : ℝ) : ℂ)))
      = q i j / ((s : ℝ) : ℂ) := by
    intro i
    have hcol : (q * q) i j = ∑ k, q i k * q k j := Matrix.mul_apply
    rw [hq.isIdempotentElem.eq] at hcol
    have hstep : (∑ k, q i k * (q k j / ((s : ℝ) : ℂ)))
        = (∑ k, q i k * q k j) / ((s : ℝ) : ℂ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => (mul_div_assoc _ _ _).symm
    rw [hstep, ← hcol]
  exact ⟨_, hx, rankOneProj_absorbed hq hx hfix⟩

/-- **A trace-one projection is `x xᴴ` for a unit vector `x`.**

`q - P` is a projection of trace zero, hence zero.  No spectral theorem is used. -/
theorem eq_rankOneProj_of_trace_one {n : Type*} [Fintype n] {q : Matrix n n ℂ}
    (hq : IsStarProjection q) (ht : q.trace = 1) :
    ∃ x ∈ unitVectors n, q = rankOneProj x := by
  have hne : q ≠ 0 := by
    intro h
    rw [h, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  obtain ⟨j, hj⟩ := exists_column_ne_zero hne
  obtain ⟨x, hxu, hqP, hPq⟩ := exists_rankOneProj_absorbed hq hj
  refine ⟨x, hxu, ?_⟩
  have hPproj : IsStarProjection (rankOneProj x) := isStarProjection_rankOneProj hxu
  have hR : IsStarProjection (q - rankOneProj x) := isStarProjection_sub hq hPproj hqP hPq
  have hRt : (q - rankOneProj x).trace = 0 := by
    rw [Matrix.trace_sub, ht, trace_rankOneProj hxu, sub_self]
  exact sub_eq_zero.mp (proj_eq_zero_of_trace_eq_zero hR hRt)

/-- Peeling one rank-one summand off a nonzero projection lowers the trace by one. -/
theorem exists_sub_rankOneProj {n : Type*} [Fintype n] {q : Matrix n n ℂ}
    (hq : IsStarProjection q) (hne : q ≠ 0) :
    ∃ P : Matrix n n ℂ, IsStarProjection (q - P) ∧ (q - P).trace = q.trace - 1 := by
  obtain ⟨j, hj⟩ := exists_column_ne_zero hne
  obtain ⟨x, hxu, hqP, hPq⟩ := exists_rankOneProj_absorbed hq hj
  refine ⟨rankOneProj x, isStarProjection_sub hq (isStarProjection_rankOneProj hxu) hqP hPq, ?_⟩
  rw [Matrix.trace_sub, trace_rankOneProj hxu]

private theorem exists_natCast_trace_aux {n : Type*} [Fintype n] :
    ∀ (N : ℕ) (q : Matrix n n ℂ), IsStarProjection q →
      (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) ≤ N → ∃ m : ℕ, q.trace = (m : ℂ) := by
  intro N
  induction N with
  | zero =>
      intro q hq hle
      have hnn : (0 : ℝ) ≤ ∑ j, ∑ k, ‖q k j‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => proj_column_nonneg q j
      have hz : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 0 := le_antisymm (by simpa using hle) hnn
      refine ⟨0, ?_⟩
      rw [proj_trace_eq hq, hz]
      simp
  | succ N ih =>
      intro q hq hle
      by_cases hz : q = 0
      · exact ⟨0, by rw [hz, Matrix.trace_zero]; simp⟩
      · obtain ⟨P, hsub, htr⟩ := exists_sub_rankOneProj hq hz
        have hb : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hle
        have hle' : (∑ j, ∑ k, ‖(q - P) k j‖ ^ 2 : ℝ) ≤ N := by
          have h1 : ((∑ j, ∑ k, ‖(q - P) k j‖ ^ 2 : ℝ) : ℂ)
              = (((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) - 1 : ℝ) : ℂ) := by
            rw [← proj_trace_eq hsub, htr, proj_trace_eq hq]
            push_cast
            ring
          have h2 : (∑ j, ∑ k, ‖(q - P) k j‖ ^ 2 : ℝ)
              = (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) - 1 := by exact_mod_cast h1
          rw [h2]
          linarith
        obtain ⟨m, hm⟩ := ih (q - P) hsub hle'
        refine ⟨m + 1, ?_⟩
        have hqt : q.trace = (q - P).trace + 1 := by rw [htr]; ring
        rw [hqt, hm]
        push_cast
        ring

/-- **The trace of a projection over `ℂ` is a natural number** — its rank.

Proved without the spectral theorem: peel off rank-one subprojections
(`STW59.exists_sub_rankOneProj`), each of which lowers the total squared norm of the
entries by exactly one, and induct on a bound for that quantity. -/
theorem exists_natCast_trace {n : Type*} [Fintype n] {q : Matrix n n ℂ}
    (hq : IsStarProjection q) : ∃ m : ℕ, q.trace = (m : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ)
  exact exists_natCast_trace_aux N q hq hN

/-! ### The model of complex projective space -/

/-- The concrete model of `ℂP^d`: rank-one orthogonal projections on `ℂ^{d+1}`. -/
def cpSet (d : ℕ) : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  {q | qᴴ = q ∧ q * q = q ∧ q.trace = 1}

theorem mem_cpSet_iff {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} :
    q ∈ cpSet d ↔ qᴴ = q ∧ q * q = q ∧ q.trace = 1 := Iff.rfl

theorem isStarProjection_of_mem_cpSet {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hq : q ∈ cpSet d) : IsStarProjection q :=
  isStarProjection_matrix_iff.mpr ⟨hq.1, hq.2.1⟩

theorem trace_of_mem_cpSet {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hq : q ∈ cpSet d) : q.trace = 1 := hq.2.2

theorem rankOneProj_mem_cpSet {d : ℕ} {x : Fin (d + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (d + 1))) : rankOneProj x ∈ cpSet d :=
  ⟨conjTranspose_eq_of_isStarProjection (isStarProjection_rankOneProj hx),
    (isStarProjection_rankOneProj hx).isIdempotentElem.eq, trace_rankOneProj hx⟩

/-- `ℂP^d` is exactly the image of the unit sphere of `ℂ^{d+1}` under `x ↦ x xᴴ`. -/
theorem cpSet_eq_image (d : ℕ) :
    cpSet d = rankOneProj '' unitVectors (Fin (d + 1)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      eq_rankOneProj_of_trace_one (isStarProjection_of_mem_cpSet hq) (trace_of_mem_cpSet hq)
    exact ⟨x, hx, hxq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact rankOneProj_mem_cpSet hx

/-- The map `x ↦ x xᴴ` from the unit sphere of `ℂ^{d+1}` onto `ℂP^d` is surjective. -/
theorem surjOn_rankOneProj (d : ℕ) :
    Set.SurjOn rankOneProj (unitVectors (Fin (d + 1))) (cpSet d) :=
  (cpSet_eq_image d).le

theorem isClosed_cpSet (d : ℕ) : IsClosed (cpSet d) := by
  have h1 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | qᴴ = q} :=
    isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have h2 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q * q = q} :=
    isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id
  -- `Continuous.matrix_trace` DOES exist at pin 81a5d257: it is declared at
  -- `Mathlib/Topology/Instances/Matrix.lean:208`, right after `Continuous.matrix_diag`,
  -- and is `@[continuity, fun_prop]`.  Do not replace it with a `simp only [Matrix.trace]`
  -- unfolding: that simp call makes no progress here and is a build error.
  have h3 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q.trace = 1} :=
    isClosed_eq (continuous_id.matrix_trace) continuous_const
  have hset : cpSet d = {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | qᴴ = q} ∩
      ({q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q * q = q} ∩
        {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q.trace = 1}) := rfl
  rw [hset]
  exact h1.inter (h2.inter h3)

theorem isCompact_cpSet (d : ℕ) : IsCompact (cpSet d) := by
  have hball : IsCompact ((Metric.closedBall (0 : ℂ) 1).matrix :
      Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) :=
    IsCompact.matrix (isCompact_closedBall 0 1)
  refine hball.of_isClosed_subset (isClosed_cpSet d) ?_
  intro q hq i j
  simpa [Metric.mem_closedBall, dist_zero_right] using
    proj_norm_entry_le_one (isStarProjection_of_mem_cpSet hq) (trace_of_mem_cpSet hq) i j

theorem cpSet_nonempty (d : ℕ) : (cpSet d).Nonempty := by
  classical
  refine ⟨rankOneProj (fun i : Fin (d + 1) => if i = 0 then (1 : ℂ) else 0),
    rankOneProj_mem_cpSet ?_⟩
  show (∑ i : Fin (d + 1), ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1
  rw [Finset.sum_eq_single (0 : Fin (d + 1))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

/-- **The model of complex projective space** `ℂP^d`, as a subspace of a matrix space. -/
abbrev CP (d : ℕ) := ↥(cpSet d)

instance CP.instCompactSpace (d : ℕ) : CompactSpace (CP d) :=
  isCompact_iff_compactSpace.mp (isCompact_cpSet d)

instance CP.instNonempty (d : ℕ) : Nonempty (CP d) :=
  Set.Nonempty.to_subtype (cpSet_nonempty d)

/-- **The tautological projection**, as a matrix-valued continuous map.  On this model
of `ℂP^d` the projection onto the tautological line is literally the inclusion
`Subtype.val`. -/
def taut (d : ℕ) : C(CP d, Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem taut_apply (d : ℕ) (z : CP d) :
    taut d z = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := rfl

theorem isStarProjection_taut (d : ℕ) (z : CP d) : IsStarProjection (taut d z) :=
  isStarProjection_of_mem_cpSet z.2

theorem trace_taut (d : ℕ) (z : CP d) : (taut d z).trace = 1 :=
  trace_of_mem_cpSet z.2

/-- The tautological line has rank one at every point: it is `x xᴴ` for a unit vector. -/
theorem taut_eq_rankOneProj (d : ℕ) (z : CP d) :
    ∃ x ∈ unitVectors (Fin (d + 1)), taut d z = rankOneProj x :=
  eq_rankOneProj_of_trace_one (isStarProjection_taut d z) (trace_taut d z)

/-! ### Matrices over a function algebra, and pointwise evaluation

The rest of the LIX development presents bundles as projections in
`Matrix ι ι C(X, ℂ)`, matching `GroupApproximation/KTheory/MatrixProjection.lean`.  This
section supplies the bridge to the pointwise linear algebra above. -/

section MatEval

variable {X : Type*} [TopologicalSpace X] {ι κ ρ : Type*}

/-- Evaluation of a (possibly rectangular) matrix of continuous scalar functions at a
point of the base. -/
def matEval (x : X) (M : Matrix ι κ C(X, ℂ)) : Matrix ι κ ℂ :=
  Matrix.of fun i j => M i j x

@[simp]
theorem matEval_apply (x : X) (M : Matrix ι κ C(X, ℂ)) (i : ι) (j : κ) :
    matEval x M i j = M i j x := rfl

/-- Two matrices of continuous functions agree as soon as they agree at every point. -/
theorem matrix_ext_of_matEval {M N : Matrix ι κ C(X, ℂ)}
    (h : ∀ x, matEval x M = matEval x N) : M = N :=
  Matrix.ext fun i j => ContinuousMap.ext fun x => congrFun (congrFun (h x) i) j

theorem matEval_mul [Fintype κ] (x : X) (M : Matrix ι κ C(X, ℂ)) (N : Matrix κ ρ C(X, ℂ)) :
    matEval x (M * N) = matEval x M * matEval x N := by
  refine Matrix.ext fun i j => ?_
  have h1 : matEval x (M * N) i j
      = (ContinuousMap.evalAlgHom ℂ ℂ x) (∑ k, M i k * N k j) := rfl
  have h2 : (matEval x M * matEval x N) i j
      = ∑ k, matEval x M i k * matEval x N k j := Matrix.mul_apply
  rw [h1, h2, map_sum]
  exact Finset.sum_congr rfl fun k _ => rfl

@[simp]
theorem matEval_conjTranspose (x : X) (M : Matrix ι κ C(X, ℂ)) :
    matEval x Mᴴ = (matEval x M)ᴴ :=
  Matrix.ext fun _ _ => rfl

@[simp]
theorem matEval_one [DecidableEq ι] (x : X) :
    matEval x (1 : Matrix ι ι C(X, ℂ)) = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

@[simp]
theorem matEval_zero (x : X) : matEval x (0 : Matrix ι κ C(X, ℂ)) = 0 :=
  Matrix.ext fun _ _ => rfl

@[simp]
theorem matEval_sub (x : X) (M N : Matrix ι κ C(X, ℂ)) :
    matEval x (M - N) = matEval x M - matEval x N :=
  Matrix.ext fun _ _ => rfl

theorem trace_matEval [Fintype ι] (x : X) (M : Matrix ι ι C(X, ℂ)) :
    (matEval x M).trace = (Matrix.trace M) x := by
  have h1 : (matEval x M).trace = ∑ i, M i i x := rfl
  have h2 : (Matrix.trace M) x = ∑ i, M i i x := by
    show (ContinuousMap.evalAlgHom ℂ ℂ x) (∑ i, M i i) = ∑ i, M i i x
    exact map_sum (ContinuousMap.evalAlgHom ℂ ℂ x) (fun i => M i i) Finset.univ
  rw [h1, h2]

variable [Fintype ι]

/-- A matrix of continuous functions is a projection exactly when it is one at every
point of the base. -/
theorem isStarProjection_of_forall_matEval {M : Matrix ι ι C(X, ℂ)}
    (h : ∀ x, IsStarProjection (matEval x M)) : IsStarProjection M := by
  rw [isStarProjection_matrix_iff]
  constructor
  · refine matrix_ext_of_matEval fun x => ?_
    rw [matEval_conjTranspose]
    exact conjTranspose_eq_of_isStarProjection (h x)
  · refine matrix_ext_of_matEval fun x => ?_
    rw [matEval_mul]
    exact (h x).isIdempotentElem.eq

theorem isStarProjection_matEval {M : Matrix ι ι C(X, ℂ)} (h : IsStarProjection M)
    (x : X) : IsStarProjection (matEval x M) := by
  rw [isStarProjection_matrix_iff]
  refine ⟨?_, ?_⟩
  · rw [← matEval_conjTranspose, conjTranspose_eq_of_isStarProjection h]
  · rw [← matEval_mul, h.isIdempotentElem.eq]

end MatEval

/-! ### The tautological line as a projection over the function algebra -/

/-- The tautological projection of `ℂP^d`, as a projection in the matrix algebra over
`C(ℂP^d, ℂ)`.  This is the LIX construction's line bundle `L`. -/
def tautMat (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) C(CP d, ℂ) :=
  Matrix.of fun i j =>
    ⟨fun z => (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j,
      (continuous_subtype_val).matrix_elem i j⟩

@[simp]
theorem tautMat_apply (d : ℕ) (i j : Fin (d + 1)) (z : CP d) :
    tautMat d i j z = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j := rfl

@[simp]
theorem matEval_tautMat (d : ℕ) (z : CP d) : matEval z (tautMat d) = taut d z :=
  Matrix.ext fun _ _ => rfl

theorem isStarProjection_tautMat (d : ℕ) : IsStarProjection (tautMat d) := by
  refine isStarProjection_of_forall_matEval fun z => ?_
  rw [matEval_tautMat]
  exact isStarProjection_taut d z

theorem trace_tautMat (d : ℕ) : Matrix.trace (tautMat d) = 1 := by
  refine ContinuousMap.ext fun z => ?_
  rw [← trace_matEval, matEval_tautMat, trace_taut]
  rfl

end

end STW59
end GroupApproximation
