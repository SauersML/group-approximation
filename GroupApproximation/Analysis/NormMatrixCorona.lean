import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The algebraic norm-matrix corona

The numerator constructed here is the genuine C-star algebra of uniformly
operator-norm-bounded sequences of finite square complex matrices.  It is the
dependent `ℓ∞` space supplied by mathlib, with pointwise ring and star
operations.  The denominator is the genuine two-sided star-stable ideal of
sequences whose operator norms tend to zero along the cofinite filter.

The quotient carries the genuine quotient norm.  We prove directly that the
noncommutative quotient multiplication is submultiplicative, that the `c₀`
ideal is closed, and hence that the quotient is a complete normed ring.  The
star and C-star layers are constructed below rather than inferred from the
commutative ideal-quotient instance in mathlib.
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

omit [∀ n, Nonempty (X n)] in
private theorem boundedMatrixSequence_coord_norm_le (a : BoundedMatrixSequence X) (n : ℕ) :
    ‖a n‖ ≤ ‖a‖ :=
  (lp.isLUB_norm a).1 ⟨n, rfl⟩

private theorem boundedMatrixSequence_coord_dist_le
    (a b : BoundedMatrixSequence X) (n : ℕ) :
    dist (a n) (b n) ≤ dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(a - b) n‖ ≤ ‖a - b‖
  exact boundedMatrixSequence_coord_norm_le X (a - b) n

/-- The c0 ideal is closed in the uniform operator norm. -/
theorem isClosed_c0MatrixSequenceIdeal :
    IsClosed (c0MatrixSequenceIdeal X : Set (BoundedMatrixSequence X)) := by
  apply IsSeqClosed.isClosed
  intro s a hs hsa
  change IsC0MatrixSequence X a
  rw [IsC0MatrixSequence, Metric.tendsto_nhds]
  intro ε hε
  have hclose : ∀ᶠ k in atTop, dist (s k) a < ε / 2 :=
    (Metric.tendsto_nhds.mp hsa) (ε / 2) (half_pos hε)
  obtain ⟨k, hk⟩ := hclose.exists
  have hsk : IsC0MatrixSequence X (s k) := by
    exact hs k
  have htail : ∀ᶠ n in cofinite, ‖s k n‖ < ε / 2 :=
    (Metric.tendsto_nhds.mp hsk) (ε / 2) (half_pos hε) |>.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_norm] using hn
  filter_upwards [htail] with n hn
  rw [Real.dist_eq, sub_zero, abs_norm]
  calc
    ‖a n‖ ≤ ‖a n - s k n‖ + ‖s k n‖ := by
      nth_rewrite 1 [← sub_add_cancel (a n) (s k n)]
      exact norm_add_le _ _
    _ < ε := by
      have hcoord : ‖a n - s k n‖ < ε / 2 := by
        calc
          ‖a n - s k n‖ = dist (a n) (s k n) := by rw [dist_eq_norm]
          _ ≤ dist a (s k) := boundedMatrixSequence_coord_dist_le X a (s k) n
          _ = dist (s k) a := dist_comm _ _
          _ < ε / 2 := hk
      linarith

noncomputable instance c0MatrixSequenceIdeal_isClosed :
    IsClosed (c0MatrixSequenceIdeal X : Set (BoundedMatrixSequence X)) :=
  isClosed_c0MatrixSequenceIdeal X

/-- The actual quotient `ℓ∞(M_{d_n}) / c₀(M_{d_n})`. -/
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

/-- Because the c0 ideal is closed, the quotient seminorm is a norm. -/
noncomputable instance normMatrixCoronaAlgebraNormedRing :
    NormedRing (NormMatrixCoronaAlgebra X) :=
  { normMatrixCoronaAlgebraSeminormedRing X,
    Submodule.Quotient.normedAddCommGroup (c0MatrixSequenceIdeal X) with }

/-- The normed matrix-corona algebra is complete. -/
noncomputable instance normMatrixCoronaAlgebraCompleteSpace :
    CompleteSpace (NormMatrixCoronaAlgebra X) :=
  Submodule.Quotient.completeSpace (c0MatrixSequenceIdeal X)

private def boundedMatrixSequenceStarHom :
    BoundedMatrixSequence X →+ NormMatrixCoronaAlgebra X :=
  (Ideal.Quotient.mk (c0MatrixSequenceIdeal X)).toAddMonoidHom.comp
    starAddEquiv.toAddMonoidHom

private theorem c0MatrixSequenceIdeal_le_star_ker :
    (c0MatrixSequenceIdeal X).toAddSubgroup ≤
      (boundedMatrixSequenceStarHom X).ker := by
  intro a ha
  change Ideal.Quotient.mk (c0MatrixSequenceIdeal X) (star a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact c0MatrixSequenceIdeal_star_mem X ha

/-- Coordinatewise adjoint descends to the matrix-corona quotient. -/
noncomputable instance normMatrixCoronaAlgebraStar :
    Star (NormMatrixCoronaAlgebra X) where
  star := QuotientAddGroup.lift
    (c0MatrixSequenceIdeal X).toAddSubgroup
    (boundedMatrixSequenceStarHom X)
    (c0MatrixSequenceIdeal_le_star_ker X)

@[simp] theorem normMatrixCorona_star_mk (a : BoundedMatrixSequence X) :
    star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a) =
      Ideal.Quotient.mk (c0MatrixSequenceIdeal X) (star a) :=
  QuotientAddGroup.lift_mk _ _ _

noncomputable instance normMatrixCoronaAlgebraInvolutiveStar :
    InvolutiveStar (NormMatrixCoronaAlgebra X) where
  star_involutive x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change star (star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a)) =
        Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a
      rw [normMatrixCorona_star_mk, normMatrixCorona_star_mk, star_star]

noncomputable instance normMatrixCoronaAlgebraStarAddMonoid :
    StarAddMonoid (NormMatrixCoronaAlgebra X) where
  star_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) (a + b)) =
          star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a) +
            star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) b)
        rw [normMatrixCorona_star_mk, normMatrixCorona_star_mk,
          normMatrixCorona_star_mk, star_add]
        rfl

noncomputable instance normMatrixCoronaAlgebraStarMul :
    StarMul (NormMatrixCoronaAlgebra X) where
  star_mul x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) (a * b)) =
          star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) b) *
            star (Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a)
        rw [normMatrixCorona_star_mk, normMatrixCorona_star_mk,
          normMatrixCorona_star_mk]
        rw [show star (a * b) = star b * star a from StarMul.star_mul a b]
        rfl

private theorem normMatrixCorona_norm_star_le (x : NormMatrixCoronaAlgebra X) :
    ‖star x‖ ≤ ‖x‖ := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ := normMatrixCorona_exists_rep_norm_lt X x hε
  rw [normMatrixCorona_star_mk]
  exact ((normMatrixCorona_norm_mk_le X (star a)).trans_lt (by simpa using ha)).le

noncomputable instance normMatrixCoronaAlgebraNormedStarGroup :
    NormedStarGroup (NormMatrixCoronaAlgebra X) where
  norm_star_le := normMatrixCorona_norm_star_le X

/-- Audit pin: the descended adjoint is an isometry for the quotient norm. -/
theorem norm_normMatrixCorona_star (x : NormMatrixCoronaAlgebra X) :
    ‖star x‖ = ‖x‖ :=
  norm_star x

private def boundedMatrixSequenceTail (a : BoundedMatrixSequence X) (N : ℕ) :
    BoundedMatrixSequence X :=
  ⟨fun n ↦ if N ≤ n then a n else 0,
    (lp.memℓp a).mono' fun n ↦ by
      split_ifs
      · exact le_rfl
      · simp⟩

omit [∀ n, Nonempty (X n)] in
@[simp] private theorem boundedMatrixSequenceTail_apply
    (a : BoundedMatrixSequence X) (N n : ℕ) :
    boundedMatrixSequenceTail X a N n = if N ≤ n then a n else 0 :=
  rfl

omit [∀ n, Nonempty (X n)] in
private theorem boundedMatrixSequence_sub_tail_isC0
    (a : BoundedMatrixSequence X) (N : ℕ) :
    IsC0MatrixSequence X (a - boundedMatrixSequenceTail X a N) := by
  rw [IsC0MatrixSequence]
  rw [Nat.cofinite_eq_atTop]
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [boundedMatrixSequenceTail_apply, hn]

private def matrixSequenceTailNorm (a : BoundedMatrixSequence X) : ℝ :=
  Filter.limsup (fun n ↦ ‖a n‖) atTop

omit [∀ n, Nonempty (X n)] in
private theorem matrixNorm_isBoundedUnder (a : BoundedMatrixSequence X) :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ ↦ ‖a n‖) :=
  ⟨‖a‖, show ∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ ‖a‖ from
    Eventually.of_forall fun n ↦ boundedMatrixSequence_coord_norm_le X a n⟩

omit [∀ n, Nonempty (X n)] in
private theorem matrixNorm_isCoboundedUnder (a : BoundedMatrixSequence X) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ ↦ ‖a n‖) :=
  Filter.isCoboundedUnder_le_of_le atTop fun n ↦ norm_nonneg (a n)

private theorem matrixSequenceTailNorm_nonneg (a : BoundedMatrixSequence X) :
    0 ≤ matrixSequenceTailNorm X a := by
  apply (Filter.le_limsup_iff
    (matrixNorm_isCoboundedUnder X a) (matrixNorm_isBoundedUnder X a)).mpr
  intro y hy
  exact Frequently.of_forall fun n ↦ hy.trans_le (norm_nonneg (a n))

private theorem matrixSequenceTailNorm_le_norm (a : BoundedMatrixSequence X) :
    matrixSequenceTailNorm X a ≤ ‖a‖ := by
  apply (Filter.limsup_le_iff
    (matrixNorm_isCoboundedUnder X a) (matrixNorm_isBoundedUnder X a)).mpr
  intro y hy
  exact Eventually.of_forall fun n ↦
    (boundedMatrixSequence_coord_norm_le X a n).trans_lt hy

omit [∀ n, Nonempty (X n)] in
private theorem norm_tail_le_add (a : BoundedMatrixSequence X)
    {N : ℕ} {c : ℝ} (hc : 0 ≤ c) (hN : ∀ n ≥ N, ‖a n‖ < c) :
    ‖boundedMatrixSequenceTail X a N‖ ≤ c := by
  rw [boundedMatrixSequence_norm_eq_ciSup]
  apply ciSup_le
  intro n
  simp only [boundedMatrixSequenceTail_apply]
  split_ifs with hn
  · exact (hN n hn).le
  · simpa using hc

private theorem normMatrixCorona_mk_le_tailNorm
    (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ ≤
      matrixSequenceTailNorm X a := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ n in atTop,
      ‖a n‖ < matrixSequenceTailNorm X a + ε :=
    Filter.eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε)
      (matrixNorm_isBoundedUnder X a)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hev)
  have hquot : Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a =
      Ideal.Quotient.mk (c0MatrixSequenceIdeal X)
        (boundedMatrixSequenceTail X a N) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact boundedMatrixSequence_sub_tail_isC0 X a N
  rw [hquot]
  exact (normMatrixCorona_norm_mk_le X _).trans
    (norm_tail_le_add X a
      (add_nonneg (matrixSequenceTailNorm_nonneg X a) hε.le) hN)

omit [∀ n, Nonempty (X n)] in
private theorem matrixSequenceTailNorm_le_norm_of_sub_isC0
    (a b : BoundedMatrixSequence X)
    (hab : a - b ∈ c0MatrixSequenceIdeal X) :
    matrixSequenceTailNorm X a ≤ ‖b‖ := by
  have hdiff : Tendsto (fun n ↦ ‖(a - b) n‖) atTop (nhds 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hab
  apply (Filter.limsup_le_iff
    (matrixNorm_isCoboundedUnder X a) (matrixNorm_isBoundedUnder X a)).mpr
  intro y hy
  have hpos : 0 < y - ‖b‖ := sub_pos.mpr hy
  have hev : ∀ᶠ n in atTop, ‖(a - b) n‖ < y - ‖b‖ :=
    (Metric.tendsto_nhds.mp hdiff) (y - ‖b‖) hpos |>.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_norm] using hn
  filter_upwards [hev] with n hn
  calc
    ‖a n‖ ≤ ‖b n‖ + ‖(a - b) n‖ := by
      nth_rewrite 1 [← add_sub_cancel (b n) (a n)]
      rw [norm_sub_rev]
      exact norm_add_le _ _
    _ ≤ ‖b‖ + ‖(a - b) n‖ :=
      add_le_add_right (boundedMatrixSequence_coord_norm_le X b n) _
    _ < ‖b‖ + (y - ‖b‖) := add_lt_add_left hn _
    _ = y := add_sub_cancel_left _ _

omit [∀ n, Nonempty (X n)] in
private theorem matrixSequenceTailNorm_le_normMatrixCorona_mk
    (a : BoundedMatrixSequence X) :
    matrixSequenceTailNorm X a ≤
      ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ := by
  apply (QuotientAddGroup.le_norm_iff).mpr
  intro b hb
  apply matrixSequenceTailNorm_le_norm_of_sub_isC0 X a b
  have hba : b - a ∈ c0MatrixSequenceIdeal X := by
    change Ideal.Quotient.mk (c0MatrixSequenceIdeal X) b =
      Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a at hb
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem b a).mp hb
  simpa [neg_sub] using (c0MatrixSequenceIdeal X).neg_mem hba

/-- The quotient norm is exactly the limsup of the coordinate operator norms.
This is the concrete norm formula for the norm-matrix corona. -/
theorem norm_normMatrixCorona_mk_eq_limsup
    (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) atTop :=
  le_antisymm (normMatrixCorona_mk_le_tailNorm X a)
    (matrixSequenceTailNorm_le_normMatrixCorona_mk X a)

private theorem limsup_matrixNorm_sq (a : BoundedMatrixSequence X) :
    (Filter.limsup (fun n ↦ ‖a n‖) atTop) ^ 2 =
      Filter.limsup (fun n ↦ ‖a n‖ ^ 2) atTop := by
  have hmono : Monotone (fun x : ℝ ↦ (max x 0) ^ 2) := by
    intro x y hxy
    have hmax : max x 0 ≤ max y 0 := max_le_max_right 0 hxy
    have hx : 0 ≤ max x 0 := le_max_right x 0
    have hy : 0 ≤ max y 0 := le_max_right y 0
    nlinarith
  have hcont : Continuous (fun x : ℝ ↦ (max x 0) ^ 2) :=
    (continuous_id.max continuous_const).pow 2
  have hmap := hmono.map_limsup_of_continuousAt
    (F := atTop) (fun n ↦ ‖a n‖) hcont.continuousAt
    (matrixNorm_isBoundedUnder X a) (matrixNorm_isCoboundedUnder X a)
  simpa [Function.comp_def, max_eq_left, matrixSequenceTailNorm_nonneg X a]
    using hmap

noncomputable instance normMatrixCoronaAlgebraCStarRing :
    CStarRing (NormMatrixCoronaAlgebra X) where
  norm_mul_self_le x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      rw [normMatrixCorona_star_mk]
      change
        ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ *
            ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) a‖ ≤
          ‖Ideal.Quotient.mk (c0MatrixSequenceIdeal X) (star a * a)‖
      rw [norm_normMatrixCorona_mk_eq_limsup,
        norm_normMatrixCorona_mk_eq_limsup]
      rw [← pow_two]
      rw [limsup_matrixNorm_sq X a]
      apply le_of_eq
      congr 1
      funext n
      exact norm_star_mul_self

/-- Audit pin: the concrete quotient norm satisfies the C-star identity. -/
theorem norm_normMatrixCorona_star_mul_self
    (x : NormMatrixCoronaAlgebra X) :
    ‖star x * x‖ = ‖x‖ ^ 2 := by
  simpa [pow_two] using (norm_star_mul_self (x := x))

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
