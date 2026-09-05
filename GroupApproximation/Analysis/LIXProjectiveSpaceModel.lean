import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

/-!
# A concrete matrix model of complex projective space

This file supplies the geometric base spaces for the STW Problem LIX counterexample
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`)
**without any vector-bundle library**.

Complex projective space is modelled as a space of matrices:

`CP d := {q : Matrix (Fin (d+1)) (Fin (d+1)) ℂ // qᴴ = q ∧ q * q = q ∧ q.trace = 1}`

carrying the subspace topology of the product topology on `Matrix (Fin (d+1)) (Fin (d+1)) ℂ`
(`Mathlib/Topology/Instances/Matrix.lean`; no norm is required, and none of the
non-instance matrix norms is opened here).  This is a homeomorphic model of `CP^d`: a
point of `CP^d` is a complex line in `ℂ^{d+1}`, and a line is the same thing as the
orthogonal projection onto it, i.e. a self-adjoint idempotent of trace one.

The decisive advantage for formalization is that the **tautological line bundle's
projection is literally `Subtype.val`** (`STW59.taut` below): a continuous
projection-valued matrix function on the base, with no quotient topology and no bundle
theory.  All Chern-class data downstream is carried by honest matrix-valued functions.

## Main definitions

* `STW59.IsProj q` — `q` is a self-adjoint idempotent matrix over `ℂ`.
* `STW59.unitVectors m` — the unit sphere of `ℂ^m`, as the subset
  `{x : Fin m → ℂ | ∑ i, ‖x i‖ ^ 2 = 1}` of the product space `Fin m → ℂ`.
* `STW59.rankOne x` — the matrix `x xᴴ`.
* `STW59.cpSet d`, `STW59.CP d` — the model of `CP^d` and its subtype.
* `STW59.taut d` — the tautological projection-valued map, `Subtype.val`.

## Main results

* `STW59.isCompact_cpSet`, `STW59.CP.instCompactSpace`, `STW59.CP.instNonempty` — the
  model is a nonempty compact Hausdorff space (Hausdorffness is the ambient
  `T2Space (Matrix m n ℂ)` instance, inherited by the subtype).
* `STW59.IsProj.eq_rankOne_of_trace_one` — a trace-one projection *is* `x xᴴ` for a unit
  vector `x`; this is the "rank one" content, proved elementarily (no spectral theorem).
* `STW59.cpSet_eq_image` — `CP^d` is exactly the image of the unit sphere of `ℂ^{d+1}`
  under the continuous map `x ↦ x xᴴ`.

## Model choices other lanes must match

* Vectors are plain functions `Fin m → ℂ`, **not** `EuclideanSpace ℂ (Fin m)`; the unit
  sphere is the set `unitVectors m` cut out by `∑ i, ‖x i‖ ^ 2 = 1`.  This avoids `PiLp`
  entirely.
* Matrices carry the product (Pi) topology from `Mathlib/Topology/Instances/Matrix.lean`.
* `CP d` uses matrices of size `d + 1`, i.e. `CP d` models `ℂP^d`.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix

noncomputable section

/-- `star z * z` is the (real) squared modulus of `z`. -/
theorem star_mul_self_eq_normSq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.normSq_eq_conj_mul_self.symm

/-- `z * star z` is the (real) squared modulus of `z`. -/
theorem mul_star_self_eq_normSq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]; exact star_mul_self_eq_normSq z

/-- An *orthogonal projection*: a self-adjoint idempotent matrix over `ℂ`.

This is the repo's stand-in for "a subbundle of a trivial bundle": a projection-valued
function on a base space is exactly the datum of a complex vector bundle presented as a
summand of a trivial one. -/
def IsProj {n : Type*} (q : Matrix n n ℂ) : Prop := qᴴ = q ∧ q * q = q

namespace IsProj

variable {n : Type*} [Fintype n] {q : Matrix n n ℂ}

theorem herm (hq : IsProj q) : qᴴ = q := hq.1

theorem idem (hq : IsProj q) : q * q = q := hq.2

theorem isHermitian (hq : IsProj q) : q.IsHermitian := hq.1

/-- The entries of a projection are conjugate-symmetric. -/
theorem entry_symm (hq : IsProj q) (i j : n) : q i j = star (q j i) := by
  have h := congrFun (congrFun hq.1 i) j
  rw [Matrix.conjTranspose_apply] at h
  exact h.symm

/-- Every diagonal entry of a projection is the squared norm of its column.  In
particular it is a nonnegative real number. -/
theorem diag_eq (hq : IsProj q) (j : n) :
    q j j = ((∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : (q * q) j j = ∑ k, q j k * q k j := Matrix.mul_apply
  rw [hq.2] at h1
  rw [h1, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hq.entry_symm j k]
  exact star_mul_self_eq_normSq (q k j)

/-- The trace of a projection is the total squared norm of its entries. -/
theorem trace_eq (hq : IsProj q) :
    q.trace = ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply]
  exact hq.diag_eq j

/-- A projection with vanishing trace is zero.  This is the elementary substitute for
the spectral theorem used throughout this file. -/
theorem eq_zero_of_trace_eq_zero (hq : IsProj q) (h : q.trace = 0) : q = 0 := by
  have h1 : ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    rw [← hq.trace_eq, h, Complex.ofReal_zero]
  have h2 : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1
  ext i j
  have hnn : ∀ j' ∈ (Finset.univ : Finset n), (0 : ℝ) ≤ ∑ k, ‖q k j'‖ ^ 2 :=
    fun j' _ => Finset.sum_nonneg fun k _ => by positivity
  have h3 : ∑ k, ‖q k j‖ ^ 2 = 0 :=
    le_antisymm (h2 ▸ Finset.single_le_sum hnn (Finset.mem_univ j)) (hnn j (Finset.mem_univ j))
  have h4 : ‖q i j‖ ^ 2 = 0 :=
    le_antisymm (h3 ▸ Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ i))
      (by positivity)
  have : ‖q i j‖ = 0 := by nlinarith [norm_nonneg (q i j)]
  simpa using this

/-- Total squared norm of the entries of a trace-one projection. -/
theorem sum_sq_eq_one (hq : IsProj q) (ht : q.trace = 1) :
    (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 1 := by
  have h1 : ((∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [← hq.trace_eq, ht, Complex.ofReal_one]
  exact_mod_cast h1

/-- Every entry of a trace-one projection has norm at most one; this is the boundedness
that makes the model of `CP^d` compact. -/
theorem norm_entry_le_one (hq : IsProj q) (ht : q.trace = 1) (i j : n) : ‖q i j‖ ≤ 1 := by
  have hnn : ∀ j' ∈ (Finset.univ : Finset n), (0 : ℝ) ≤ ∑ k, ‖q k j'‖ ^ 2 :=
    fun j' _ => Finset.sum_nonneg fun k _ => by positivity
  have h1 : (∑ k, ‖q k j‖ ^ 2) ≤ 1 :=
    (hq.sum_sq_eq_one ht) ▸ Finset.single_le_sum hnn (Finset.mem_univ j)
  have h2 : ‖q i j‖ ^ 2 ≤ ∑ k, ‖q k j‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (q i j)]

end IsProj

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
def rankOne {m : ℕ} (x : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.vecMulVec x (star x)

@[simp]
theorem rankOne_apply {m : ℕ} (x : Fin m → ℂ) (i j : Fin m) :
    rankOne x i j = x i * star (x j) := rfl

theorem isProj_rankOne {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ unitVectors m) :
    IsProj (rankOne x) := by
  constructor
  · ext i j
    rw [Matrix.conjTranspose_apply, rankOne_apply, rankOne_apply, star_mul, star_star,
      mul_comm]
  · ext i j
    rw [Matrix.mul_apply]
    have hre : ∀ k, rankOne x i k * rankOne x k j
        = (x i * star (x j)) * (star (x k) * x k) := by
      intro k
      rw [rankOne_apply, rankOne_apply]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hre k), ← Finset.mul_sum, sum_star_mul_self hx,
      mul_one, rankOne_apply]

theorem trace_rankOne {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ unitVectors m) :
    (rankOne x).trace = 1 := by
  rw [Matrix.trace]
  have : ∀ i, Matrix.diag (rankOne x) i = star (x i) * x i := by
    intro i; rw [Matrix.diag_apply, rankOne_apply, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => this i), sum_star_mul_self hx]

theorem continuous_rankOne (m : ℕ) : Continuous (rankOne : (Fin m → ℂ) → _) := by
  refine continuous_matrix fun i j => ?_
  simp only [rankOne_apply]
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
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Metric.mem_closedBall, dist_zero_right]
  intro i _
  have hsum : ∑ i, ‖x i‖ ^ 2 = 1 := hx
  have h2 : ‖x i‖ ^ 2 ≤ 1 :=
    hsum ▸ Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (x i)]

/-! ### Rank-one-ness of trace-one projections -/

/-- **A trace-one projection is `x xᴴ` for a unit vector `x`.**

The proof is elementary: normalize any nonzero column `u = q · j`, form the rank-one
projection `P = x xᴴ`, check `q P = P` and `P q = P`, and conclude that `q - P` is a
projection of trace zero, hence zero (`IsProj.eq_zero_of_trace_eq_zero`).  No spectral
theorem and no rank/trace theory is used. -/
theorem IsProj.eq_rankOne_of_trace_one {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hq : IsProj q) (ht : q.trace = 1) : ∃ x ∈ unitVectors (d + 1), q = rankOne x := by
  classical
  have hnn : ∀ j' : Fin (d + 1), (0 : ℝ) ≤ ∑ k, ‖q k j'‖ ^ 2 :=
    fun j' => Finset.sum_nonneg fun k _ => by positivity
  have hsum : (∑ j, ∑ k, ‖q k j‖ ^ 2 : ℝ) = 1 := hq.sum_sq_eq_one ht
  -- pick a column with nonzero norm
  obtain ⟨j, hj⟩ : ∃ j : Fin (d + 1), (∑ k, ‖q k j‖ ^ 2) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_congr rfl (fun j _ => hcon j), Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  have hjpos : 0 < ∑ k, ‖q k j‖ ^ 2 := lt_of_le_of_ne (hnn j) (Ne.symm hj)
  set c : ℝ := ∑ k, ‖q k j‖ ^ 2 with hc
  set s : ℝ := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hjpos
  have hs2 : s * s = c := Real.mul_self_sqrt hjpos.le
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hs0)
  -- the normalized column
  refine ⟨fun i => q i j / ((s : ℝ) : ℂ), ?_, ?_⟩
  · -- it is a unit vector
    have hnorms : ‖((s : ℝ) : ℂ)‖ = s := Complex.norm_of_nonneg hs0.le
    have hterm : ∀ i : Fin (d + 1), ‖q i j / ((s : ℝ) : ℂ)‖ ^ 2 = ‖q i j‖ ^ 2 / (s * s) := by
      intro i
      rw [norm_div, hnorms, div_pow, ← sq]
      ring_nf
    rw [show (∑ i, ‖q i j / ((s : ℝ) : ℂ)‖ ^ 2) = ∑ i, ‖q i j‖ ^ 2 / (s * s) from
      Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div, hs2]
    have : (∑ i, ‖q i j‖ ^ 2) = c := by rw [hc]
    rw [this, div_self hj]
  · -- it reproduces `q`
    set x : Fin (d + 1) → ℂ := fun i => q i j / ((s : ℝ) : ℂ) with hx
    have hxu : x ∈ unitVectors (d + 1) := by
      have hnorms : ‖((s : ℝ) : ℂ)‖ = s := Complex.norm_of_nonneg hs0.le
      have hterm : ∀ i : Fin (d + 1), ‖q i j / ((s : ℝ) : ℂ)‖ ^ 2 = ‖q i j‖ ^ 2 / (s * s) := by
        intro i
        rw [norm_div, hnorms, div_pow, ← sq]
        ring_nf
      show (∑ i, ‖x i‖ ^ 2) = 1
      rw [hx]
      rw [show (∑ i, ‖q i j / ((s : ℝ) : ℂ)‖ ^ 2) = ∑ i, ‖q i j‖ ^ 2 / (s * s) from
        Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div, hs2]
      have : (∑ i, ‖q i j‖ ^ 2) = c := by rw [hc]
      rw [this, div_self hj]
    have hPproj : IsProj (rankOne x) := isProj_rankOne hxu
    have hPtrace : (rankOne x).trace = 1 := trace_rankOne hxu
    -- `q` fixes the normalized column
    have hfix : ∀ i, (∑ k, q i k * x k) = x i := by
      intro i
      have hcol : (q * q) i j = ∑ k, q i k * q k j := Matrix.mul_apply
      rw [hq.2] at hcol
      have : (∑ k, q i k * x k) = (∑ k, q i k * q k j) / ((s : ℝ) : ℂ) := by
        rw [hx, Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc]
      rw [this, ← hcol, hx]
    have hqP : q * rankOne x = rankOne x := by
      ext i i'
      rw [Matrix.mul_apply]
      have hre : ∀ k, q i k * rankOne x k i' = (q i k * x k) * star (x i') := by
        intro k; rw [rankOne_apply]; ring
      rw [Finset.sum_congr rfl (fun k _ => hre k), ← Finset.sum_mul, hfix i, rankOne_apply]
    have hPq : rankOne x * q = rankOne x := by
      have h1 : (q * rankOne x)ᴴ = (rankOne x)ᴴ := congrArg _ hqP
      rw [Matrix.conjTranspose_mul, hPproj.1, hq.1] at h1
      exact h1
    have hR : IsProj (q - rankOne x) := by
      constructor
      · rw [Matrix.conjTranspose_sub, hq.1, hPproj.1]
      · have : (q - rankOne x) * (q - rankOne x)
            = q * q - q * rankOne x - rankOne x * q + rankOne x * rankOne x := by
          noncomm_ring
        rw [this, hq.2, hPproj.2, hqP, hPq]
        abel
    have hRt : (q - rankOne x).trace = 0 := by
      rw [Matrix.trace_sub, ht, hPtrace, sub_self]
    have := hR.eq_zero_of_trace_eq_zero hRt
    exact sub_eq_zero.mp this

/-! ### The model of complex projective space -/

/-- The concrete model of `ℂP^d`: rank-one orthogonal projections on `ℂ^{d+1}`. -/
def cpSet (d : ℕ) : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  {q | qᴴ = q ∧ q * q = q ∧ q.trace = 1}

theorem mem_cpSet_iff {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} :
    q ∈ cpSet d ↔ qᴴ = q ∧ q * q = q ∧ q.trace = 1 := Iff.rfl

theorem isProj_of_mem_cpSet {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hq : q ∈ cpSet d) : IsProj q := ⟨hq.1, hq.2.1⟩

theorem trace_of_mem_cpSet {d : ℕ} {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hq : q ∈ cpSet d) : q.trace = 1 := hq.2.2

theorem rankOne_mem_cpSet {d : ℕ} {x : Fin (d + 1) → ℂ} (hx : x ∈ unitVectors (d + 1)) :
    rankOne x ∈ cpSet d :=
  ⟨(isProj_rankOne hx).1, (isProj_rankOne hx).2, trace_rankOne hx⟩

/-- `ℂP^d` is exactly the image of the unit sphere of `ℂ^{d+1}` under `x ↦ x xᴴ`. -/
theorem cpSet_eq_image (d : ℕ) : cpSet d = rankOne '' unitVectors (d + 1) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (isProj_of_mem_cpSet hq).eq_rankOne_of_trace_one (trace_of_mem_cpSet hq)
    exact ⟨x, hx, hxq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact rankOne_mem_cpSet hx

/-- The map `x ↦ x xᴴ` from the unit sphere of `ℂ^{d+1}` onto `ℂP^d` is surjective. -/
theorem surjOn_rankOne (d : ℕ) : Set.SurjOn rankOne (unitVectors (d + 1)) (cpSet d) :=
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
  intro q hq
  intro i j
  simpa [Metric.mem_closedBall, dist_zero_right] using
    (isProj_of_mem_cpSet hq).norm_entry_le_one (trace_of_mem_cpSet hq) i j

theorem cpSet_nonempty (d : ℕ) : (cpSet d).Nonempty := by
  classical
  refine ⟨rankOne (Pi.single 0 1), rankOne_mem_cpSet ?_⟩
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

/-- **The tautological projection.**  On this model of `ℂP^d` the projection onto the
tautological line is literally the inclusion `Subtype.val`: a continuous
projection-valued matrix function.  This is the whole point of the model — no quotient
topology and no bundle library are needed. -/
def taut (d : ℕ) : C(CP d, Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem taut_apply (d : ℕ) (z : CP d) : taut d z = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  rfl

theorem taut_isProj (d : ℕ) (z : CP d) : IsProj (taut d z) :=
  isProj_of_mem_cpSet z.2

theorem taut_trace (d : ℕ) (z : CP d) : (taut d z).trace = 1 :=
  trace_of_mem_cpSet z.2

/-- The tautological line has rank one at every point: it is `x xᴴ` for a unit vector. -/
theorem taut_eq_rankOne (d : ℕ) (z : CP d) :
    ∃ x ∈ unitVectors (d + 1), taut d z = rankOne x :=
  (taut_isProj d z).eq_rankOne_of_trace_one (taut_trace d z)

end

end STW59
end GroupApproximation
