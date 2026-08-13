import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The algebraic norm-matrix corona

This file constructs the actual algebra quotient underlying the norm-matrix
corona.  Its numerator is the star subalgebra of uniformly bounded sequences
of finite square complex matrices, and its denominator is the two-sided ideal
of sequences converging to zero in operator norm along the cofinite filter.

Mathlib currently supplies a normed quotient instance only for ideals in
commutative normed rings.  Matrix algebras are noncommutative, so this file
does **not** manufacture a `CStarAlgebra` instance for the quotient.  The
quotient below is nevertheless the genuine ring/algebra quotient, not a
record of consequences that a hypothetical embedding would have.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]

noncomputable section

/-- Uniform operator-norm boundedness for a varying sequence of square
matrices. -/
def IsUniformlyBoundedMatrixSequence
    (a : ∀ n, Matrix (X n) (X n) ℂ) : Prop :=
  ∃ C : ℝ, ∀ n, ‖a n‖ ≤ C

namespace IsUniformlyBoundedMatrixSequence

theorem zero : IsUniformlyBoundedMatrixSequence X 0 := by
  refine ⟨0, fun n ↦ ?_⟩
  simp

theorem one : IsUniformlyBoundedMatrixSequence X 1 := by
  refine ⟨max ‖(1 : Matrix (X 0) (X 0) ℂ)‖ 1, fun n ↦ ?_⟩
  by_cases h : Nonempty (X n)
  · letI := h
    rw [show (1 : ∀ n, Matrix (X n) (X n) ℂ) n = 1 from rfl, norm_one]
    exact le_max_right _ _
  · haveI : IsEmpty (X n) := not_nonempty_iff.mp h
    have hzero : (1 : Matrix (X n) (X n) ℂ) = 0 := by ext i; exact isEmptyElim i
    rw [show (1 : ∀ n, Matrix (X n) (X n) ℂ) n = 1 from rfl, hzero, norm_zero]
    exact (norm_nonneg _).trans (le_max_left _ _)

theorem add {a b : ∀ n, Matrix (X n) (X n) ℂ}
    (ha : IsUniformlyBoundedMatrixSequence X a)
    (hb : IsUniformlyBoundedMatrixSequence X b) :
    IsUniformlyBoundedMatrixSequence X (a + b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  refine ⟨A + B, fun n ↦ ?_⟩
  exact (norm_add_le (a n) (b n)).trans (add_le_add (hA n) (hB n))

theorem mul {a b : ∀ n, Matrix (X n) (X n) ℂ}
    (ha : IsUniformlyBoundedMatrixSequence X a)
    (hb : IsUniformlyBoundedMatrixSequence X b) :
    IsUniformlyBoundedMatrixSequence X (a * b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  refine ⟨|A| * |B|, fun n ↦ ?_⟩
  refine (norm_mul_le (a n) (b n)).trans ?_
  exact mul_le_mul (le_trans (hA n) (le_abs_self A))
    (le_trans (hB n) (le_abs_self B)) (norm_nonneg _) (abs_nonneg _)

theorem algebraMap (z : ℂ) :
    IsUniformlyBoundedMatrixSequence X (algebraMap ℂ (∀ n, Matrix (X n) (X n) ℂ) z) := by
  have hone := one X
  obtain ⟨C, hC⟩ := hone
  refine ⟨‖z‖ * C, fun n ↦ ?_⟩
  simp only [Pi.algebraMap_apply]
  rw [Algebra.algebraMap_eq_smul_one]
  exact (norm_smul_le z (1 : Matrix (X n) (X n) ℂ)).trans
    (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg z))

theorem star {a : ∀ n, Matrix (X n) (X n) ℂ}
    (ha : IsUniformlyBoundedMatrixSequence X a) :
    IsUniformlyBoundedMatrixSequence X (star a) := by
  obtain ⟨A, hA⟩ := ha
  refine ⟨A, fun n ↦ ?_⟩
  simpa using hA n

end IsUniformlyBoundedMatrixSequence

/-- The star algebra of uniformly operator-norm bounded matrix sequences. -/
def boundedMatrixSequenceAlgebra :
    StarSubalgebra ℂ (∀ n, Matrix (X n) (X n) ℂ) where
  carrier := {a | IsUniformlyBoundedMatrixSequence X a}
  zero_mem' := IsUniformlyBoundedMatrixSequence.zero X
  one_mem' := IsUniformlyBoundedMatrixSequence.one X
  add_mem' := IsUniformlyBoundedMatrixSequence.add X
  mul_mem' := IsUniformlyBoundedMatrixSequence.mul X
  algebraMap_mem' := IsUniformlyBoundedMatrixSequence.algebraMap X
  star_mem' := IsUniformlyBoundedMatrixSequence.star X

/-- A bounded sequence of finite square complex matrices. -/
abbrev BoundedMatrixSequence := boundedMatrixSequenceAlgebra X

@[simp] theorem boundedMatrixSequence_coe_apply
    (a : BoundedMatrixSequence X) (n : ℕ) :
    ((a : ∀ n, Matrix (X n) (X n) ℂ) n) = a.1 n := rfl

/-- A bounded matrix sequence is `c₀` when its operator norm tends to zero
along the cofinite filter. -/
def IsC0MatrixSequence (a : BoundedMatrixSequence X) : Prop :=
  Tendsto (fun n ↦ ‖a.1 n‖) cofinite (nhds 0)

namespace IsC0MatrixSequence

theorem zero : IsC0MatrixSequence X 0 := by
  simp [IsC0MatrixSequence]

theorem add {a b : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) (hb : IsC0MatrixSequence X b) :
    IsC0MatrixSequence X (a + b) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a + b).1 n))
  · filter_upwards with n
    exact norm_add_le _ _
  · simpa only [add_zero] using Filter.Tendsto.add ha hb

theorem neg {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) : IsC0MatrixSequence X (-a) := by
  simpa [IsC0MatrixSequence] using ha

theorem mul_left (b : BoundedMatrixSequence X) {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) : IsC0MatrixSequence X (b * a) := by
  obtain ⟨B, hB⟩ := b.2
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((b * a).1 n))
  · filter_upwards with n
    exact (norm_mul_le (b.1 n) (a.1 n)).trans
      (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))
  · simpa only [IsC0MatrixSequence, mul_zero] using
      (tendsto_const_nhds.mul ha)

theorem mul_right {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) (b : BoundedMatrixSequence X) :
    IsC0MatrixSequence X (a * b) := by
  obtain ⟨B, hB⟩ := b.2
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a * b).1 n))
  · filter_upwards with n
    exact (norm_mul_le (a.1 n) (b.1 n)).trans
      (mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _))
  · simpa only [IsC0MatrixSequence, zero_mul] using
      (ha.mul tendsto_const_nhds)

theorem star {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) : IsC0MatrixSequence X (star a) := by
  simpa [IsC0MatrixSequence] using ha

end IsC0MatrixSequence

/-- The genuine two-sided `c₀` ideal inside the bounded matrix-sequence
algebra. -/
def c0MatrixSequenceIdeal : Ideal (BoundedMatrixSequence X) where
  carrier := {a | IsC0MatrixSequence X a}
  zero_mem' := IsC0MatrixSequence.zero X
  add_mem' := IsC0MatrixSequence.add X
  smul_mem' := fun b _ ha ↦ IsC0MatrixSequence.mul_left X b ha

instance c0MatrixSequenceIdeal_isTwoSided :
    (c0MatrixSequenceIdeal X).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ IsC0MatrixSequence.mul_right X ha b

/-- The actual algebra quotient `ℓ∞(M_{d_n}) / c₀(M_{d_n})`.

No normed- or C-star-algebra instance is asserted here: mathlib's quotient
norm API currently covers commutative ideals only. -/
abbrev NormMatrixCorona :=
  BoundedMatrixSequence X ⧸ c0MatrixSequenceIdeal X

/-- The quotient map from bounded sequences to the norm-matrix corona. -/
def normMatrixCoronaMk : BoundedMatrixSequence X →+* NormMatrixCorona X :=
  Ideal.Quotient.mk (c0MatrixSequenceIdeal X)

@[simp] theorem normMatrixCoronaMk_apply (a : BoundedMatrixSequence X) :
    normMatrixCoronaMk X a = Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a := rfl

theorem normMatrixCoronaMk_eq_zero_iff (a : BoundedMatrixSequence X) :
    normMatrixCoronaMk X a = 0 ↔ IsC0MatrixSequence X a := by
  change Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rfl

end

end GroupApproximation
