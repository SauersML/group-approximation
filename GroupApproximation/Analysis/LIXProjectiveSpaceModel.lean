import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Star.StarProjection

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
* `STW59.matEval x` is the evaluation `*`-algebra map
  `Matrix ι ι C(X, ℂ) →ₐ[ℂ] Matrix ι ι ℂ` at a point; it is the bridge between the
  "matrix over the function algebra" picture and the pointwise linear algebra.
* Vectors are plain functions `Fin m → ℂ`, **not** `EuclideanSpace ℂ (Fin m)`; the unit
  sphere is `STW59.unitVectors m`, cut out by `∑ i, ‖x i‖ ^ 2 = 1`.  This avoids `PiLp`
  entirely.
* `CP d` uses matrices of size `d + 1`, i.e. `CP d` models `ℂP^d`.

## Main results

* `STW59.isCompact_cpSet`, `STW59.CP.instCompactSpace`, `STW59.CP.instNonempty` — the
  model is a nonempty compact Hausdorff space (Hausdorffness is the ambient
  `T2Space (Matrix m n ℂ)` instance, inherited by the subtype).
* `STW59.eq_rankOne_of_trace_one` — a trace-one projection *is* `x xᴴ` for a unit
  vector `x`; this is the "rank one" content, proved elementarily.  The route replaces
  the spectral theorem by `STW59.proj_eq_zero_of_trace_eq_zero`: a projection whose
  trace vanishes is zero, because its trace is the total squared norm of its entries.
* `STW59.cpSet_eq_image` — `ℂP^d` is exactly the image of the unit sphere of `ℂ^{d+1}`
  under the continuous map `x ↦ x xᴴ`.
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

/-! ### Projections over `ℂ`, entrywise

Mathlib's `IsStarProjection` is used throughout; no new predicate is introduced.  For a
square complex matrix `star q = qᴴ`, so `IsStarProjection q` is exactly
`qᴴ = q ∧ q * q = q`. -/

section Entrywise

variable {n : Type*} [Fintype n] {q : Matrix n n ℂ}

theorem conjTranspose_eq_of_isStarProjection (hq : IsStarProjection q) : qᴴ = q := by
  rw [← Matrix.star_eq_conjTranspose]
  exact hq.isSelfAdjoint.star_eq

theorem isStarProjection_matrix_iff :
    IsStarProjection q ↔ qᴴ = q ∧ q * q = q := by
  rw [isStarProjection_iff']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← Matrix.star_eq_conjTranspose]; exact h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by rw [Matrix.star_eq_conjTranspose]; exact h1⟩

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
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply]
  exact proj_diag_eq hq j

/-- **A projection with vanishing trace is zero.**  This is the elementary substitute
for the spectral theorem used throughout this file. -/
theorem proj_eq_zero_of_trace_eq_zero (hq : IsStarProjection q) (h : q.trace = 0) :
    q = 0 := by
  have h1 : ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    rw [← proj_trace_eq hq, h, Complex.ofReal_zero]
  have h2 : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1
  have hnn : ∀ j' ∈ (Finset.univ : Finset n), (0 : ℝ) ≤ ∑ k, ‖q k j'‖ ^ 2 :=
    fun j' _ => Finset.sum_nonneg fun k _ => by positivity
  ext i j
  have h3 : ∑ k, ‖q k j‖ ^ 2 = 0 :=
    le_antisymm (h2 ▸ Finset.single_le_sum hnn (Finset.mem_univ j)) (hnn j (Finset.mem_univ j))
  have h4 : ‖q i j‖ ^ 2 = 0 :=
    le_antisymm (h3 ▸ Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ i))
      (by positivity)
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
  have hnn : ∀ j' ∈ (Finset.univ : Finset n), (0 : ℝ) ≤ ∑ k, ‖q k j'‖ ^ 2 :=
    fun j' _ => Finset.sum_nonneg fun k _ => by positivity
  have h1 : (∑ k, ‖q k j‖ ^ 2) ≤ 1 :=
    (proj_sum_sq_eq_one hq ht) ▸ Finset.single_le_sum hnn (Finset.mem_univ j)
  have h2 : ‖q i j‖ ^ 2 ≤ ∑ k, ‖q k j‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (q i j)]

end Entrywise

/-! ### Unit vectors and rank-one projections -/

/-- The unit sphere of `ℂ^m`, as a subset of the product space `Fin m → ℂ`.

Model choice: vectors are plain functions, so no `PiLp`/`EuclideanSpace` instance is
involved anywhere in this development. -/
def unitVectors (m : ℕ) : Set (Fin m → ℂ) := {x | ∑ i, ‖x i‖ ^ 2 = 1}

theorem mem_unitVectors_iff {m : ℕ} {x : Fin m → ℂ} :
    x ∈ unitVectors m ↔ ∑ i, ‖x i‖ ^ 2 = 1 := Iff.rfl

/-- For `x` a unit vector, `∑ k, star (x k) * x k = 1` in `ℂ`. -/
theorem sum_star_mul_self {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ unitVectors m) :
    ∑ k, star (x k) * x k = 1 := by
  have h : ∑ k, star (x k) * x k = ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => star_mul_self_eq_normSq (x k)
  rw [h, mem_unitVectors_iff.mp hx, Complex.ofReal_one]

/-- The rank-one matrix `x xᴴ`. -/
def rankOneProj {m : ℕ} (x : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.vecMulVec x (star x)

@[simp]
theorem rankOneProj_apply {m : ℕ} (x : Fin m → ℂ) (i j : Fin m) :
    rankOneProj x i j = x i * star (x j) := rfl

theorem isStarProjection_rankOneProj {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ unitVectors m) :
    IsStarProjection (rankOneProj x) := by
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

theorem trace_rankOneProj {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ unitVectors m) :
    (rankOneProj x).trace = 1 := by
  rw [Matrix.trace]
  have h : ∀ i, Matrix.diag (rankOneProj x) i = star (x i) * x i := by
    intro i; rw [Matrix.diag_apply, rankOneProj_apply, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => h i), sum_star_mul_self hx]

theorem continuous_rankOneProj (m : ℕ) : Continuous (rankOneProj : (Fin m → ℂ) → _) := by
  refine continuous_matrix fun i j => ?_
  simp only [rankOneProj_apply]
  exact (continuous_apply i).mul ((continuous_apply j).star)

theorem isClosed_unitVectors (m : ℕ) : IsClosed (unitVectors m) := by
  have hcont : Continuous fun x : Fin m → ℂ => ∑ i, ‖x i‖ ^ 2 :=
    continuous_finset_sum _ fun i _ => ((continuous_apply i).norm).pow 2
  simpa [unitVectors] using isClosed_eq hcont continuous_const

theorem isCompact_unitVectors (m : ℕ) : IsCompact (unitVectors m) := by
  have hball : IsCompact (Set.univ.pi fun _ : Fin m => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hball.of_isClosed_subset (isClosed_unitVectors m) ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Metric.mem_closedBall,
    dist_zero_right]
  intro i _
  have hsum : ∑ i, ‖x i‖ ^ 2 = 1 := hx
  have h2 : ‖x i‖ ^ 2 ≤ 1 :=
    hsum ▸ Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (x i)]

/-! ### Rank-one-ness of trace-one projections -/

/-- **A trace-one projection is `x xᴴ` for a unit vector `x`.**

The proof is elementary: normalize any nonzero column `u = q · j`, form the rank-one
projection `P = x xᴴ`, check `q P = P` and `P q = P`, and conclude that `q - P` is a
projection of trace zero, hence zero (`proj_eq_zero_of_trace_eq_zero`).  No spectral
theorem and no rank/trace theory is used. -/
theorem eq_rankOneProj_of_trace_one {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hq : IsStarProjection q) (ht : q.trace = 1) :
    ∃ x ∈ unitVectors (d + 1), q = rankOneProj x := by
  classical
  have hnn : ∀ j' : Fin (d + 1), (0 : ℝ) ≤ ∑ k, ‖q k j'‖ ^ 2 :=
    fun j' => Finset.sum_nonneg fun k _ => by positivity
  have hsum : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 1 := proj_sum_sq_eq_one hq ht
  obtain ⟨j, hj⟩ : ∃ j : Fin (d + 1), (∑ k, ‖q k j‖ ^ 2) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_congr rfl (fun j _ => hcon j), Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  have hjpos : 0 < ∑ k, ‖q k j‖ ^ 2 := lt_of_le_of_ne (hnn j) (Ne.symm hj)
  have hs0 : 0 < Real.sqrt (∑ k, ‖q k j‖ ^ 2) := Real.sqrt_pos.mpr hjpos
  have hs2 : Real.sqrt (∑ k, ‖q k j‖ ^ 2) * Real.sqrt (∑ k, ‖q k j‖ ^ 2)
      = ∑ k, ‖q k j‖ ^ 2 := Real.mul_self_sqrt hjpos.le
  have hnorms : ‖((Real.sqrt (∑ k, ‖q k j‖ ^ 2) : ℝ) : ℂ)‖
      = Real.sqrt (∑ k, ‖q k j‖ ^ 2) := Complex.norm_of_nonneg hs0.le
  set s : ℂ := ((Real.sqrt (∑ k, ‖q k j‖ ^ 2) : ℝ) : ℂ) with hsdef
  have hsne : s ≠ 0 := by
    rw [hsdef]
    simpa using ne_of_gt hs0
  set x : Fin (d + 1) → ℂ := fun i => q i j / s with hxdef
  have hxu : x ∈ unitVectors (d + 1) := by
    show (∑ i, ‖x i‖ ^ 2) = 1
    have hterm : ∀ i : Fin (d + 1),
        ‖x i‖ ^ 2 = ‖q i j‖ ^ 2 / (Real.sqrt (∑ k, ‖q k j‖ ^ 2)
          * Real.sqrt (∑ k, ‖q k j‖ ^ 2)) := by
      intro i
      rw [hxdef, norm_div, hsdef, hnorms, div_pow, ← sq]
      ring_nf
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div, hs2, div_self hj]
  refine ⟨x, hxu, ?_⟩
  have hPproj : IsStarProjection (rankOneProj x) := isStarProjection_rankOneProj hxu
  have hPtrace : (rankOneProj x).trace = 1 := trace_rankOneProj hxu
  have hfix : ∀ i, (∑ k, q i k * x k) = x i := by
    intro i
    have hcol : (q * q) i j = ∑ k, q i k * q k j := Matrix.mul_apply
    rw [hq.isIdempotentElem.eq] at hcol
    have hstep : (∑ k, q i k * x k) = (∑ k, q i k * q k j) / s := by
      rw [hxdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc]
    rw [hstep, ← hcol, hxdef]
  have hqP : q * rankOneProj x = rankOneProj x := by
    ext i i'
    rw [Matrix.mul_apply]
    have hre : ∀ k, q i k * rankOneProj x k i' = (q i k * x k) * star (x i') := by
      intro k; rw [rankOneProj_apply]; ring
    rw [Finset.sum_congr rfl (fun k _ => hre k), ← Finset.sum_mul, hfix i, rankOneProj_apply]
  have hPq : rankOneProj x * q = rankOneProj x := by
    have h1 : (q * rankOneProj x)ᴴ = (rankOneProj x)ᴴ := congrArg _ hqP
    rw [Matrix.conjTranspose_mul, conjTranspose_eq_of_isStarProjection hPproj,
      conjTranspose_eq_of_isStarProjection hq] at h1
    exact h1
  have hR : IsStarProjection (q - rankOneProj x) := by
    rw [isStarProjection_matrix_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_sub, conjTranspose_eq_of_isStarProjection hq,
        conjTranspose_eq_of_isStarProjection hPproj]
    · have hexp : (q - rankOneProj x) * (q - rankOneProj x)
          = q * q - q * rankOneProj x - rankOneProj x * q
            + rankOneProj x * rankOneProj x := by
        noncomm_ring
      rw [hexp, hq.isIdempotentElem.eq, hPproj.isIdempotentElem.eq, hqP, hPq]
      abel
  have hRt : (q - rankOneProj x).trace = 0 := by
    rw [Matrix.trace_sub, ht, hPtrace, sub_self]
  exact sub_eq_zero.mp (proj_eq_zero_of_trace_eq_zero hR hRt)

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
    (hx : x ∈ unitVectors (d + 1)) : rankOneProj x ∈ cpSet d :=
  ⟨conjTranspose_eq_of_isStarProjection (isStarProjection_rankOneProj hx),
    (isStarProjection_rankOneProj hx).isIdempotentElem.eq, trace_rankOneProj hx⟩

/-- `ℂP^d` is exactly the image of the unit sphere of `ℂ^{d+1}` under `x ↦ x xᴴ`. -/
theorem cpSet_eq_image (d : ℕ) : cpSet d = rankOneProj '' unitVectors (d + 1) := by
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
    Set.SurjOn rankOneProj (unitVectors (d + 1)) (cpSet d) :=
  (cpSet_eq_image d).le

theorem isClosed_cpSet (d : ℕ) : IsClosed (cpSet d) := by
  have h1 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | qᴴ = q} :=
    isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have h2 : IsClosed {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ | q * q = q} :=
    isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id
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
  refine ⟨rankOneProj (Pi.single 0 1), rankOneProj_mem_cpSet ?_⟩
  show (∑ i, ‖(Pi.single (0 : Fin (d + 1)) (1 : ℂ)) i‖ ^ 2) = 1
  rw [Finset.sum_eq_single (0 : Fin (d + 1))]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
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
    ∃ x ∈ unitVectors (d + 1), taut d z = rankOneProj x :=
  eq_rankOneProj_of_trace_one (isStarProjection_taut d z) (trace_taut d z)

/-! ### Matrices over a function algebra, and pointwise evaluation

The rest of the LIX development presents bundles as projections in
`Matrix ι ι C(X, ℂ)`, matching `GroupApproximation/KTheory/MatrixProjection.lean`.  This
section supplies the bridge to the pointwise linear algebra above. -/

section MatEval

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of a matrix of continuous scalar functions at a point of the base,
bundled as an algebra homomorphism. -/
def matEval (x : X) : Matrix ι ι C(X, ℂ) →ₐ[ℂ] Matrix ι ι ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix

@[simp]
theorem matEval_apply (x : X) (M : Matrix ι ι C(X, ℂ)) (i j : ι) :
    matEval x M i j = M i j x := rfl

theorem matEval_conjTranspose (x : X) (M : Matrix ι ι C(X, ℂ)) :
    matEval x Mᴴ = (matEval x M)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem trace_matEval (x : X) (M : Matrix ι ι C(X, ℂ)) :
    (matEval x M).trace = (Matrix.trace M) x := by
  simp only [Matrix.trace, Matrix.diag_apply, matEval_apply]
  exact (map_sum (ContinuousMap.evalAlgHom ℂ ℂ x) (fun i => M i i) Finset.univ).symm

/-- A matrix of continuous functions is a projection exactly when it is one at every
point of the base. -/
theorem isStarProjection_of_forall_matEval {M : Matrix ι ι C(X, ℂ)}
    (h : ∀ x, IsStarProjection (matEval x M)) : IsStarProjection M := by
  rw [isStarProjection_matrix_iff]
  constructor
  · ext i j
    refine ContinuousMap.ext fun x => ?_
    have hx := conjTranspose_eq_of_isStarProjection (h x)
    have := congrFun (congrFun hx i) j
    simpa [Matrix.conjTranspose_apply] using this
  · ext i j
    refine ContinuousMap.ext fun x => ?_
    have hx := (h x).isIdempotentElem.eq
    have h1 : matEval x (M * M) = matEval x M := by rw [map_mul, hx]
    have := congrFun (congrFun h1 i) j
    simpa using this

theorem isStarProjection_matEval {M : Matrix ι ι C(X, ℂ)} (h : IsStarProjection M)
    (x : X) : IsStarProjection (matEval x M) := by
  rw [isStarProjection_matrix_iff]
  refine ⟨?_, ?_⟩
  · rw [← matEval_conjTranspose, conjTranspose_eq_of_isStarProjection h]
  · rw [← map_mul, h.isIdempotentElem.eq]

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
theorem matEval_tautMat (d : ℕ) (z : CP d) : matEval z (tautMat d) = taut d z := by
  ext i j
  rfl

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
