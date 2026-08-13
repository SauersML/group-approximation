import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The algebraic norm-matrix corona

The numerator constructed here is the genuine C-star algebra of uniformly
operator-norm-bounded sequences of finite square complex matrices.  It is the
dependent `ℓ∞` space supplied by mathlib, with pointwise ring and star
operations.  The denominator is the genuine two-sided star-stable ideal of
sequences whose operator norms tend to zero along the cofinite filter.

The final quotient in this file is at present an algebra quotient.  Mathlib's
normed ideal-quotient instance is restricted to commutative rings, while
matrix algebras are noncommutative.  We therefore do not assert a normed or
C-star structure for the quotient until that missing analytic layer is proved.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

universe u

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

noncomputable section

/-- A uniformly operator-norm-bounded sequence of finite square complex
matrices.  This is mathlib's dependent `ℓ∞` space, hence already a
complete C-star algebra. -/
abbrev BoundedMatrixSequence :=
  lp (fun n ↦ Matrix (X n) (X n) ℂ) ∞

omit [∀ n, Nonempty (X n)] in
theorem boundedMatrixSequence_norm_eq_ciSup (a : BoundedMatrixSequence X) :
    ‖a‖ = ⨆ n, ‖a n‖ :=
  lp.norm_eq_ciSup a

/-- A bounded matrix sequence is `c₀` when its coordinate operator norms
tend to zero along the cofinite filter. -/
def IsC0MatrixSequence (a : BoundedMatrixSequence X) : Prop :=
  Tendsto (fun n ↦ ‖a n‖) cofinite (nhds 0)

namespace IsC0MatrixSequence

omit [∀ n, Nonempty (X n)] in
theorem zero : IsC0MatrixSequence X 0 := by
  simp [IsC0MatrixSequence]

omit [∀ n, Nonempty (X n)] in
theorem add {a b : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) (hb : IsC0MatrixSequence X b) :
    IsC0MatrixSequence X (a + b) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a + b) n))
  · filter_upwards with n
    exact norm_add_le _ _
  · simpa only [add_zero] using Filter.Tendsto.add ha hb

omit [∀ n, Nonempty (X n)] in
theorem neg {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) : IsC0MatrixSequence X (-a) := by
  simpa [IsC0MatrixSequence] using ha

omit [∀ n, Nonempty (X n)] in
theorem mul_left (b : BoundedMatrixSequence X) {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) : IsC0MatrixSequence X (b * a) := by
  have hbdd : ∀ n, ‖b n‖ ≤ ‖b‖ := fun n ↦ (lp.isLUB_norm b).1 ⟨n, rfl⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((b * a) n))
  · filter_upwards with n
    exact (norm_mul_le (b n) (a n)).trans
      (mul_le_mul_of_nonneg_right (hbdd n) (norm_nonneg _))
  · simpa only [mul_zero] using tendsto_const_nhds.mul ha

omit [∀ n, Nonempty (X n)] in
theorem mul_right {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) (b : BoundedMatrixSequence X) :
    IsC0MatrixSequence X (a * b) := by
  have hbdd : ∀ n, ‖b n‖ ≤ ‖b‖ := fun n ↦ (lp.isLUB_norm b).1 ⟨n, rfl⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a * b) n))
  · filter_upwards with n
    exact (norm_mul_le (a n) (b n)).trans
      (mul_le_mul_of_nonneg_left (hbdd n) (norm_nonneg _))
  · simpa only [zero_mul] using ha.mul tendsto_const_nhds

omit [∀ n, Nonempty (X n)] in
theorem star {a : BoundedMatrixSequence X}
    (ha : IsC0MatrixSequence X a) : IsC0MatrixSequence X (star a) := by
  simpa [IsC0MatrixSequence, lp.star_apply] using ha

end IsC0MatrixSequence

/-- The genuine two-sided `c₀` ideal in the bounded matrix-sequence C-star
algebra. -/
def c0MatrixSequenceIdeal : Ideal (BoundedMatrixSequence X) where
  carrier := {a | IsC0MatrixSequence X a}
  zero_mem' := IsC0MatrixSequence.zero X
  add_mem' := IsC0MatrixSequence.add X
  smul_mem' := fun b _ ha ↦ IsC0MatrixSequence.mul_left X b ha

instance c0MatrixSequenceIdeal_isTwoSided :
    (c0MatrixSequenceIdeal X).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ IsC0MatrixSequence.mul_right X ha b

theorem c0MatrixSequenceIdeal_star_mem {a : BoundedMatrixSequence X}
    (ha : a ∈ c0MatrixSequenceIdeal X) :
    star a ∈ c0MatrixSequenceIdeal X :=
  IsC0MatrixSequence.star X ha

/-- The actual algebra quotient `ℓ∞(M_{d_n}) / c₀(M_{d_n})`.

No normed- or C-star-algebra instance is asserted yet; the noncommutative
quotient norm and its completeness are the next analytic layer. -/
abbrev NormMatrixCoronaAlgebra :=
  BoundedMatrixSequence X ⧸ c0MatrixSequenceIdeal X

private theorem normMatrixCorona_exists_rep_norm_lt
    (x : NormMatrixCoronaAlgebra X) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : BoundedMatrixSequence X,
      Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a = x ∧ ‖a‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

private theorem normMatrixCorona_norm_mk_le (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le (c0MatrixSequenceIdeal X) a

private theorem real_mul_continuousAt (x y : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ p.1 * p.2) (x, y) :=
  (continuous_fst.mul continuous_snd).continuousAt

/-- The quotient seminorm is submultiplicative.  This is the missing
noncommutative analogue of mathlib's commutative ideal-quotient instance. -/
noncomputable instance normMatrixCoronaAlgebraSeminormedRing :
    SeminormedRing (NormMatrixCoronaAlgebra X) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := _root_.le_of_forall_pos_le_add fun ε hε ↦ by
    obtain ⟨δ, hδ, hbound⟩ :=
      Metric.continuousAt_iff.mp (real_mul_continuousAt ‖x‖ ‖y‖) ε hε
    let ε₁ := δ / 3
    let ε₂ := δ / 3
    have hε₁ : 0 < ε₁ := div_pos hδ (by norm_num)
    have hε₂ : 0 < ε₂ := div_pos hδ (by norm_num)
    obtain ⟨a, ha_eq, ha⟩ := normMatrixCorona_exists_rep_norm_lt X x hε₁
    obtain ⟨b, hb_eq, hb⟩ := normMatrixCorona_exists_rep_norm_lt X y hε₂
    rw [← ha_eq, ← hb_eq]
    have hpair : dist (‖a‖, ‖b‖)
          (‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖,
            ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) b‖) < δ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq]
      rw [max_lt_iff]
      constructor
      · rw [abs_of_nonneg]
        · rw [← ha_eq] at ha
          dsimp [ε₁] at ha
          linarith
        · exact sub_nonneg.mpr (normMatrixCorona_norm_mk_le X a)
      · rw [abs_of_nonneg]
        · rw [← hb_eq] at hb
          dsimp [ε₂] at hb
          linarith
        · exact sub_nonneg.mpr (normMatrixCorona_norm_mk_le X b)
    have hpair' : dist (‖a‖, ‖b‖) (‖x‖, ‖y‖) < δ := by
      simpa only [ha_eq, hb_eq] using hpair
    have hprod := hbound hpair'
    simp only [Real.dist_eq] at hprod
    have hupper : ‖a‖ * ‖b‖ < ‖x‖ * ‖y‖ + ε :=
      sub_lt_iff_lt_add'.mp (abs_lt.mp hprod).2
    calc
      ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) (a * b)‖
          ≤ ‖a * b‖ := normMatrixCorona_norm_mk_le X (a * b)
      _ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b
      _ ≤ ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ *
            ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) b‖ + ε :=
        by simpa only [ha_eq, hb_eq] using hupper.le

/-- Audit pin: multiplication in the algebraic corona is genuinely controlled
by the quotient seminorm. -/
theorem norm_normMatrixCorona_mul_le (x y : NormMatrixCoronaAlgebra X) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x y

/-- The quotient map from bounded sequences to the algebraic norm-matrix
corona. -/
def normMatrixCoronaMk : BoundedMatrixSequence X →+* NormMatrixCoronaAlgebra X :=
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
