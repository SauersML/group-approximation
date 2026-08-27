import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The norm-matrix C-star corona, at an arbitrary filter

The numerator constructed here is the genuine C-star algebra of uniformly
operator-norm-bounded sequences of finite square complex matrices.  It is the
dependent `ℓ∞` space supplied by mathlib, with pointwise ring and star
operations.  The denominator is the genuine two-sided star-stable ideal of
sequences whose operator norms tend to zero **along a filter `l`**.

The quotient carries the genuine quotient norm.  We prove directly that the
noncommutative quotient multiplication is submultiplicative, that the null
ideal is closed, and hence that the quotient is a complete normed ring.  The
star and C-star layers are constructed below rather than inferred from the
commutative ideal-quotient instance in mathlib.

## Why the filter is a parameter

The manuscript's `thm:kazhdan-transport` forms `B_ω = ∏_ω B(K_n)`, the norm
ultraproduct along a *free ultrafilter*.  The development used to build only
the cofinite corona `ℓ∞/c₀`, and audited that substitution as a standing gap
(`NEW.UF.01`).  Nothing in the construction below is special to `cofinite`:
the only place the filter was used concretely is the truncation that realizes
a class by a representative of nearly minimal norm, and truncating to a *tail*
`{n | N ≤ n}` is just the case `l = atTop` of truncating to an arbitrary
member of `l`.  Carrying the filter therefore costs nothing and makes the
printed object -- the ultraproduct along `ω` -- an instance rather than a
surrogate.  Two hypotheses appear where the filter matters:

* `[l.NeBot]` for every statement about the limsup norm formula, since at
  `l = ⊥` every sequence is null and the limsup is junk;
* nothing at all for the algebra, the ideal, or the C-star structure other
  than through that formula.

`cofinite` on `ℕ` satisfies `NeBot`, so the cofinite corona -- still named
`NormMatrixCStarCorona` and still opaque -- is recovered verbatim at the end.
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

omit [∀ n, Nonempty (X n)] in
theorem boundedMatrixSequence_coord_norm_le (a : BoundedMatrixSequence X)
    (n : ℕ) : ‖a n‖ ≤ ‖a‖ :=
  (lp.isLUB_norm a).1 ⟨n, rfl⟩

variable (l : Filter ℕ)

/-- A bounded matrix sequence is null along `l` when its coordinate operator
norms tend to zero along `l`. -/
def IsNullMatrixSequence (a : BoundedMatrixSequence X) : Prop :=
  Tendsto (fun n ↦ ‖a n‖) l (nhds 0)

namespace IsNullMatrixSequence

omit [∀ n, Nonempty (X n)] in
theorem zero : IsNullMatrixSequence X l 0 := by
  rw [IsNullMatrixSequence]
  refine tendsto_const_nhds.congr fun n ↦ ?_
  simp

omit [∀ n, Nonempty (X n)] in
theorem add {a b : BoundedMatrixSequence X}
    (ha : IsNullMatrixSequence X l a) (hb : IsNullMatrixSequence X l b) :
    IsNullMatrixSequence X l (a + b) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a + b) n))
  · filter_upwards with n
    exact norm_add_le _ _
  · simpa only [add_zero] using Filter.Tendsto.add ha hb

omit [∀ n, Nonempty (X n)] in
theorem neg {a : BoundedMatrixSequence X}
    (ha : IsNullMatrixSequence X l a) : IsNullMatrixSequence X l (-a) := by
  simpa [IsNullMatrixSequence] using ha

omit [∀ n, Nonempty (X n)] in
theorem mul_left (b : BoundedMatrixSequence X) {a : BoundedMatrixSequence X}
    (ha : IsNullMatrixSequence X l a) : IsNullMatrixSequence X l (b * a) := by
  have hbdd : ∀ n, ‖b n‖ ≤ ‖b‖ := fun n ↦ (lp.isLUB_norm b).1 ⟨n, rfl⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((b * a) n))
  · filter_upwards with n
    exact (norm_mul_le (b n) (a n)).trans
      (mul_le_mul_of_nonneg_right (hbdd n) (norm_nonneg _))
  · simpa only [mul_zero] using tendsto_const_nhds.mul ha

omit [∀ n, Nonempty (X n)] in
theorem mul_right {a : BoundedMatrixSequence X}
    (ha : IsNullMatrixSequence X l a) (b : BoundedMatrixSequence X) :
    IsNullMatrixSequence X l (a * b) := by
  have hbdd : ∀ n, ‖b n‖ ≤ ‖b‖ := fun n ↦ (lp.isLUB_norm b).1 ⟨n, rfl⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a * b) n))
  · filter_upwards with n
    exact (norm_mul_le (a n) (b n)).trans
      (mul_le_mul_of_nonneg_left (hbdd n) (norm_nonneg _))
  · simpa only [zero_mul] using ha.mul tendsto_const_nhds

omit [∀ n, Nonempty (X n)] in
theorem star {a : BoundedMatrixSequence X}
    (ha : IsNullMatrixSequence X l a) : IsNullMatrixSequence X l (star a) := by
  simpa [IsNullMatrixSequence, lp.star_apply] using ha

omit [∀ n, Nonempty (X n)] in
/-- A sequence that is null along a coarser filter is null along a finer one.
This is what makes the cofinite corona map onto every `ω`-ultraproduct. -/
theorem mono {l' : Filter ℕ} (hle : l' ≤ l) {a : BoundedMatrixSequence X}
    (ha : IsNullMatrixSequence X l a) : IsNullMatrixSequence X l' a :=
  ha.mono_left hle

end IsNullMatrixSequence

/-- The genuine two-sided ideal of sequences null along `l` in the bounded
matrix-sequence C-star algebra. -/
def nullMatrixSequenceIdeal : Ideal (BoundedMatrixSequence X) where
  carrier := {a | IsNullMatrixSequence X l a}
  zero_mem' := IsNullMatrixSequence.zero X l
  add_mem' := IsNullMatrixSequence.add X l
  smul_mem' := fun b _ ha ↦ IsNullMatrixSequence.mul_left X l b ha

instance nullMatrixSequenceIdeal_isTwoSided :
    (nullMatrixSequenceIdeal X l).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ IsNullMatrixSequence.mul_right X l ha b

theorem nullMatrixSequenceIdeal_star_mem {a : BoundedMatrixSequence X}
    (ha : a ∈ nullMatrixSequenceIdeal X l) :
    star a ∈ nullMatrixSequenceIdeal X l :=
  IsNullMatrixSequence.star X l ha

private theorem boundedMatrixSequence_coord_dist_le
    (a b : BoundedMatrixSequence X) (n : ℕ) :
    dist (a n) (b n) ≤ dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(a - b) n‖ ≤ ‖a - b‖
  exact boundedMatrixSequence_coord_norm_le X (a - b) n

/-- The null ideal is closed in the uniform operator norm, at every filter. -/
theorem isClosed_nullMatrixSequenceIdeal :
    IsClosed (nullMatrixSequenceIdeal X l : Set (BoundedMatrixSequence X)) := by
  apply IsSeqClosed.isClosed
  intro s a hs hsa
  change IsNullMatrixSequence X l a
  rw [IsNullMatrixSequence, Metric.tendsto_nhds]
  intro ε hε
  have hclose : ∀ᶠ k in atTop, dist (s k) a < ε / 2 :=
    (Metric.tendsto_nhds.mp hsa) (ε / 2) (half_pos hε)
  obtain ⟨k, hk⟩ := hclose.exists
  have hsk : IsNullMatrixSequence X l (s k) := hs k
  have htail : ∀ᶠ n in l, ‖s k n‖ < ε / 2 :=
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

noncomputable instance nullMatrixSequenceIdeal_isClosed :
    IsClosed (nullMatrixSequenceIdeal X l : Set (BoundedMatrixSequence X)) :=
  isClosed_nullMatrixSequenceIdeal X l

/-- **The corona at the filter `l`**: the quotient of `ℓ∞(M_{d_n})` by the
sequences null along `l`.  At `l = cofinite` this is `ℓ∞/c₀`; at a free
ultrafilter `l = ω` it is the manuscript's norm ultraproduct
`∏_ω M_{d_n}`. -/
abbrev FilterMatrixCoronaAlgebra :=
  BoundedMatrixSequence X ⧸ nullMatrixSequenceIdeal X l

private theorem filterMatrixCorona_exists_rep_norm_lt
    (x : FilterMatrixCoronaAlgebra X l) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : BoundedMatrixSequence X,
      Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a = x ∧ ‖a‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

private theorem filterMatrixCorona_norm_mk_le (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le (nullMatrixSequenceIdeal X l) a

private theorem real_mul_continuousAt (x y : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ p.1 * p.2) (x, y) :=
  (continuous_fst.mul continuous_snd).continuousAt

/-- The quotient seminorm is submultiplicative.  This is the missing
noncommutative analogue of mathlib's commutative ideal-quotient instance. -/
noncomputable instance filterMatrixCoronaAlgebraSeminormedRing :
    SeminormedRing (FilterMatrixCoronaAlgebra X l) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := _root_.le_of_forall_pos_le_add fun ε hε ↦ by
    obtain ⟨δ, hδ, hbound⟩ :=
      Metric.continuousAt_iff.mp (real_mul_continuousAt ‖x‖ ‖y‖) ε hε
    let ε₁ := δ / 3
    let ε₂ := δ / 3
    have hε₁ : 0 < ε₁ := div_pos hδ (by norm_num)
    have hε₂ : 0 < ε₂ := div_pos hδ (by norm_num)
    obtain ⟨a, ha_eq, ha⟩ := filterMatrixCorona_exists_rep_norm_lt X l x hε₁
    obtain ⟨b, hb_eq, hb⟩ := filterMatrixCorona_exists_rep_norm_lt X l y hε₂
    rw [← ha_eq, ← hb_eq]
    have hpair : dist (‖a‖, ‖b‖)
          (‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖,
            ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) b‖) < δ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq]
      rw [max_lt_iff]
      constructor
      · rw [abs_of_nonneg]
        · rw [← ha_eq] at ha
          dsimp [ε₁] at ha
          linarith
        · exact sub_nonneg.mpr (filterMatrixCorona_norm_mk_le X l a)
      · rw [abs_of_nonneg]
        · rw [← hb_eq] at hb
          dsimp [ε₂] at hb
          linarith
        · exact sub_nonneg.mpr (filterMatrixCorona_norm_mk_le X l b)
    have hpair' : dist (‖a‖, ‖b‖) (‖x‖, ‖y‖) < δ := by
      simpa only [ha_eq, hb_eq] using hpair
    have hprod := hbound hpair'
    simp only [Real.dist_eq] at hprod
    have hupper : ‖a‖ * ‖b‖ < ‖x‖ * ‖y‖ + ε :=
      sub_lt_iff_lt_add'.mp (abs_lt.mp hprod).2
    calc
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (a * b)‖
          ≤ ‖a * b‖ := filterMatrixCorona_norm_mk_le X l (a * b)
      _ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b
      _ ≤ ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ *
            ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) b‖ + ε :=
        by simpa only [ha_eq, hb_eq] using hupper.le

/-- Because the null ideal is closed, the quotient seminorm is a norm. -/
noncomputable instance filterMatrixCoronaAlgebraNormedRing :
    NormedRing (FilterMatrixCoronaAlgebra X l) :=
  { filterMatrixCoronaAlgebraSeminormedRing X l,
    Submodule.Quotient.normedAddCommGroup (nullMatrixSequenceIdeal X l) with }

/-- The normed matrix-corona algebra is complete. -/
noncomputable instance filterMatrixCoronaAlgebraCompleteSpace :
    CompleteSpace (FilterMatrixCoronaAlgebra X l) :=
  Submodule.Quotient.completeSpace (nullMatrixSequenceIdeal X l)

private def boundedMatrixSequenceStarHom :
    BoundedMatrixSequence X →+ FilterMatrixCoronaAlgebra X l :=
  (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l)).toAddMonoidHom.comp
    starAddEquiv.toAddMonoidHom

private theorem nullMatrixSequenceIdeal_le_star_ker :
    (nullMatrixSequenceIdeal X l).toAddSubgroup ≤
      (boundedMatrixSequenceStarHom X l).ker := by
  intro a ha
  change Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (star a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact nullMatrixSequenceIdeal_star_mem X l ha

/-- Coordinatewise adjoint descends to the matrix-corona quotient. -/
noncomputable instance filterMatrixCoronaAlgebraStar :
    Star (FilterMatrixCoronaAlgebra X l) where
  star := QuotientAddGroup.lift
    (nullMatrixSequenceIdeal X l).toAddSubgroup
    (boundedMatrixSequenceStarHom X l)
    (nullMatrixSequenceIdeal_le_star_ker X l)

@[simp] theorem filterMatrixCorona_star_mk (a : BoundedMatrixSequence X) :
    star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a) =
      Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (star a) :=
  QuotientAddGroup.lift_mk _ _ _

noncomputable instance filterMatrixCoronaAlgebraInvolutiveStar :
    InvolutiveStar (FilterMatrixCoronaAlgebra X l) where
  star_involutive x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change star (star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a)) =
        Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a
      rw [filterMatrixCorona_star_mk, filterMatrixCorona_star_mk, star_star]

noncomputable instance filterMatrixCoronaAlgebraStarRing :
    StarRing (FilterMatrixCoronaAlgebra X l) where
  star_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (a + b)) =
          star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a) +
            star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) b)
        rw [filterMatrixCorona_star_mk, filterMatrixCorona_star_mk,
          filterMatrixCorona_star_mk, star_add]
        rfl
  star_mul x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (a * b)) =
          star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) b) *
            star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a)
        rw [filterMatrixCorona_star_mk, filterMatrixCorona_star_mk,
          filterMatrixCorona_star_mk]
        rw [show star (a * b) = star b * star a from StarMul.star_mul a b]
        rfl

private theorem filterMatrixCorona_norm_star_le
    (x : FilterMatrixCoronaAlgebra X l) : ‖star x‖ ≤ ‖x‖ := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ := filterMatrixCorona_exists_rep_norm_lt X l x hε
  rw [filterMatrixCorona_star_mk]
  exact ((filterMatrixCorona_norm_mk_le X l (star a)).trans_lt
    (by simpa using ha)).le

noncomputable instance filterMatrixCoronaAlgebraNormedStarGroup :
    NormedStarGroup (FilterMatrixCoronaAlgebra X l) where
  norm_star_le := filterMatrixCorona_norm_star_le X l

/-- Audit pin: the descended adjoint is an isometry for the quotient norm. -/
theorem norm_filterMatrixCorona_star (x : FilterMatrixCoronaAlgebra X l) :
    ‖star x‖ = ‖x‖ :=
  norm_star x

/-! ## The norm formula

A class is realized by a representative supported on any prescribed member of
`l`, and that is the whole of the filter dependence.  At `l = atTop` the
member can be taken to be a tail `{n | N ≤ n}`, which is how this argument is
usually written; nothing below needs that special shape. -/

open scoped Classical in
/-- The restriction of a bounded sequence to a set of indices, extended by
zero.  This is the truncation that realizes a class by a representative of
nearly minimal norm. -/
private def boundedMatrixSequenceOn (a : BoundedMatrixSequence X) (S : Set ℕ) :
    BoundedMatrixSequence X :=
  ⟨fun n ↦ if n ∈ S then a n else 0,
    (lp.memℓp a).mono' fun n ↦ by
      split_ifs
      · exact le_rfl
      · simp⟩

omit [∀ n, Nonempty (X n)] in
open scoped Classical in
@[simp] private theorem boundedMatrixSequenceOn_apply
    (a : BoundedMatrixSequence X) (S : Set ℕ) (n : ℕ) :
    boundedMatrixSequenceOn X a S n = if n ∈ S then a n else 0 :=
  rfl

omit [∀ n, Nonempty (X n)] in
private theorem boundedMatrixSequence_sub_on_isNull
    (a : BoundedMatrixSequence X) {S : Set ℕ} (hS : S ∈ l) :
    IsNullMatrixSequence X l (a - boundedMatrixSequenceOn X a S) := by
  rw [IsNullMatrixSequence]
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [hS] with n hn
  simp [boundedMatrixSequenceOn_apply, hn]

omit [∀ n, Nonempty (X n)] in
private theorem norm_boundedMatrixSequenceOn_le (a : BoundedMatrixSequence X)
    {S : Set ℕ} {c : ℝ} (hc : 0 ≤ c) (hS : ∀ n ∈ S, ‖a n‖ ≤ c) :
    ‖boundedMatrixSequenceOn X a S‖ ≤ c := by
  rw [boundedMatrixSequence_norm_eq_ciSup]
  apply ciSup_le
  intro n
  simp only [boundedMatrixSequenceOn_apply]
  split_ifs with hn
  · exact hS n hn
  · simpa using hc

/-- The candidate for the corona norm: the limsup of the coordinate operator
norms along `l`. -/
private def matrixSequenceFilterNorm (a : BoundedMatrixSequence X) : ℝ :=
  Filter.limsup (fun n ↦ ‖a n‖) l

omit [∀ n, Nonempty (X n)] in
private theorem matrixNorm_isBoundedUnder (a : BoundedMatrixSequence X) :
    IsBoundedUnder (· ≤ ·) l (fun n : ℕ ↦ ‖a n‖) :=
  ⟨‖a‖, show ∀ᶠ n : ℕ in l, ‖a n‖ ≤ ‖a‖ from
    Eventually.of_forall fun n ↦ boundedMatrixSequence_coord_norm_le X a n⟩

omit [∀ n, Nonempty (X n)] in
private theorem matrixNorm_isCoboundedUnder [l.NeBot]
    (a : BoundedMatrixSequence X) :
    IsCoboundedUnder (· ≤ ·) l (fun n : ℕ ↦ ‖a n‖) :=
  Filter.isCoboundedUnder_le_of_le l fun n ↦ norm_nonneg (a n)

omit [∀ n, Nonempty (X n)] in
private theorem matrixSequenceFilterNorm_nonneg [l.NeBot]
    (a : BoundedMatrixSequence X) : 0 ≤ matrixSequenceFilterNorm X l a := by
  apply (Filter.le_limsup_iff
    (matrixNorm_isCoboundedUnder X l a) (matrixNorm_isBoundedUnder X l a)).mpr
  intro y hy
  exact Frequently.of_forall fun n ↦ hy.trans_le (norm_nonneg (a n))

omit [∀ n, Nonempty (X n)] in
private theorem matrixSequenceFilterNorm_le_norm [l.NeBot]
    (a : BoundedMatrixSequence X) : matrixSequenceFilterNorm X l a ≤ ‖a‖ := by
  apply (Filter.limsup_le_iff
    (matrixNorm_isCoboundedUnder X l a) (matrixNorm_isBoundedUnder X l a)).mpr
  intro y hy
  exact Eventually.of_forall fun n ↦
    (boundedMatrixSequence_coord_norm_le X a n).trans_lt hy

private theorem filterMatrixCorona_mk_le_filterNorm [l.NeBot]
    (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤
      matrixSequenceFilterNorm X l a := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ n in l, ‖a n‖ < matrixSequenceFilterNorm X l a + ε :=
    Filter.eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε)
      (matrixNorm_isBoundedUnder X l a)
  have hS : {n : ℕ | ‖a n‖ < matrixSequenceFilterNorm X l a + ε} ∈ l := hev
  have hquot : Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a =
      Ideal.Quotient.mk (nullMatrixSequenceIdeal X l)
        (boundedMatrixSequenceOn X a
          {n : ℕ | ‖a n‖ < matrixSequenceFilterNorm X l a + ε}) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact boundedMatrixSequence_sub_on_isNull X l a hS
  rw [hquot]
  exact (filterMatrixCorona_norm_mk_le X l _).trans
    (norm_boundedMatrixSequenceOn_le X a
      (add_nonneg (matrixSequenceFilterNorm_nonneg X l a) hε.le)
      fun n hn ↦ le_of_lt hn)

omit [∀ n, Nonempty (X n)] in
private theorem eventually_norm_sub_lt_of_isNull
    (a b : BoundedMatrixSequence X)
    (hab : IsNullMatrixSequence X l (a - b)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in l, ‖(a - b) n‖ < c :=
  (Metric.tendsto_nhds.mp hab) c hc |>.mono fun n hn ↦ by
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn

omit [∀ n, Nonempty (X n)] in
private theorem matrixNorm_le_coordNorm_add_norm_sub
    (a b : BoundedMatrixSequence X) (n : ℕ) :
    ‖a n‖ ≤ ‖b n‖ + ‖(a - b) n‖ := by
  nth_rewrite 1 [← add_sub_cancel (b n) (a n)]
  change ‖b n + (a n - b n)‖ ≤ ‖b n‖ + ‖a n - b n‖
  exact norm_add_le _ _

omit [∀ n, Nonempty (X n)] in
private theorem matrixNorm_le_norm_add_norm_sub
    (a b : BoundedMatrixSequence X) (n : ℕ) :
    ‖a n‖ ≤ ‖b‖ + ‖(a - b) n‖ :=
  (matrixNorm_le_coordNorm_add_norm_sub X a b n).trans
    (add_le_add (boundedMatrixSequence_coord_norm_le X b n) le_rfl)

omit [∀ n, Nonempty (X n)] in
private theorem eventually_matrixNorm_lt_of_sub_isNull
    (a b : BoundedMatrixSequence X)
    (hab : IsNullMatrixSequence X l (a - b)) {y : ℝ} (hy : ‖b‖ < y) :
    ∀ᶠ n in l, ‖a n‖ < y := by
  have hev : ∀ᶠ n in l, ‖(a - b) n‖ < y - ‖b‖ :=
    eventually_norm_sub_lt_of_isNull X l a b hab (sub_pos.mpr hy)
  filter_upwards [hev] with n hn
  exact (matrixNorm_le_norm_add_norm_sub X a b n).trans_lt (by linarith)

omit [∀ n, Nonempty (X n)] in
private theorem matrixSequenceFilterNorm_le_norm_of_sub_isNull [l.NeBot]
    (a b : BoundedMatrixSequence X)
    (hab : IsNullMatrixSequence X l (a - b)) :
    matrixSequenceFilterNorm X l a ≤ ‖b‖ := by
  apply (Filter.limsup_le_iff
    (matrixNorm_isCoboundedUnder X l a) (matrixNorm_isBoundedUnder X l a)).mpr
  intro y hy
  exact eventually_matrixNorm_lt_of_sub_isNull X l a b hab hy

private theorem matrixSequenceFilterNorm_le_norm_of_mk_eq [l.NeBot]
    (a b : BoundedMatrixSequence X)
    (hb : Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) b =
      Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a) :
    matrixSequenceFilterNorm X l a ≤ ‖b‖ := by
  have hba : b - a ∈ nullMatrixSequenceIdeal X l :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem b a).mp hb
  have hab : a - b ∈ nullMatrixSequenceIdeal X l := by
    simpa [neg_sub] using (nullMatrixSequenceIdeal X l).neg_mem hba
  exact matrixSequenceFilterNorm_le_norm_of_sub_isNull X l a b hab

private theorem matrixSequenceFilterNorm_le_filterMatrixCorona_mk [l.NeBot]
    (a : BoundedMatrixSequence X) :
    matrixSequenceFilterNorm X l a ≤
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ := by
  apply (QuotientAddGroup.le_norm_iff).mpr
  intro b hb
  exact matrixSequenceFilterNorm_le_norm_of_mk_eq X l a b hb

/-- **The concrete norm formula.**  The quotient norm is exactly the limsup of
the coordinate operator norms along `l`.  At a free ultrafilter the limsup is
the ultralimit, so this is the manuscript's `‖[A_n]_ω‖ = lim_ω ‖A_n‖`. -/
theorem norm_filterMatrixCorona_mk_eq_limsup [l.NeBot]
    (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) l :=
  le_antisymm (filterMatrixCorona_mk_le_filterNorm X l a)
    (matrixSequenceFilterNorm_le_filterMatrixCorona_mk X l a)

omit [∀ n, Nonempty (X n)] in
private theorem limsup_matrixNorm_sq [l.NeBot] (a : BoundedMatrixSequence X) :
    (Filter.limsup (fun n ↦ ‖a n‖) l) ^ 2 =
      Filter.limsup (fun n ↦ ‖a n‖ ^ 2) l := by
  have hmono : Monotone (fun x : ℝ ↦ (max x 0) ^ 2) := by
    intro x y hxy
    have hmax : max x 0 ≤ max y 0 := max_le_max_right 0 hxy
    have hx : 0 ≤ max x 0 := le_max_right x 0
    have hy : 0 ≤ max y 0 := le_max_right y 0
    nlinarith
  have hcont : Continuous (fun x : ℝ ↦ (max x 0) ^ 2) :=
    (continuous_id.max continuous_const).pow 2
  have hmap := hmono.map_limsup_of_continuousAt
    (F := l) (fun n ↦ ‖a n‖) hcont.continuousAt
    (matrixNorm_isBoundedUnder X l a) (matrixNorm_isCoboundedUnder X l a)
  have htail : 0 ≤ Filter.limsup (fun n ↦ ‖a n‖) l :=
    matrixSequenceFilterNorm_nonneg X l a
  rw [max_eq_left htail] at hmap
  simpa [Function.comp_def, max_eq_left] using hmap

noncomputable instance filterMatrixCoronaAlgebraCStarRing [l.NeBot] :
    CStarRing (FilterMatrixCoronaAlgebra X l) where
  norm_mul_self_le x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change
        ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ *
            ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤
          ‖star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a) *
            Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖
      rw [filterMatrixCorona_star_mk]
      change
        ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ *
            ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤
          ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (star a * a)‖
      rw [norm_filterMatrixCorona_mk_eq_limsup,
        norm_filterMatrixCorona_mk_eq_limsup]
      rw [← pow_two]
      rw [limsup_matrixNorm_sq X l a]
      apply le_of_eq
      congr 1
      funext n
      simpa [pow_two, lp.star_apply] using
        (CStarRing.norm_star_mul_self (x := a n)).symm

/-- The quotient's existing complex algebra structure is compatible with its
quotient norm. -/
noncomputable instance filterMatrixCoronaAlgebraNormedAlgebra :
    NormedAlgebra ℂ (FilterMatrixCoronaAlgebra X l) :=
  ⟨fun z x ↦ (norm_smul z x).le⟩

/-- Coordinatewise adjoint on the quotient is conjugate-linear. -/
noncomputable instance filterMatrixCoronaAlgebraStarModule :
    StarModule ℂ (FilterMatrixCoronaAlgebra X l) := by
  constructor
  intro z x
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
      change star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) (z • a)) =
        star z • star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a)
      rw [filterMatrixCorona_star_mk, filterMatrixCorona_star_mk, star_smul]
      rfl

/-- Audit pin: the concrete quotient norm satisfies the C-star identity. -/
theorem norm_filterMatrixCorona_star_mul_self [l.NeBot]
    (x : FilterMatrixCoronaAlgebra X l) : ‖star x * x‖ = ‖x‖ ^ 2 := by
  simpa [pow_two] using (CStarRing.norm_star_mul_self (x := x))

/-- Audit pin: multiplication in the algebraic corona is genuinely controlled
by the quotient seminorm. -/
theorem norm_filterMatrixCorona_mul_le (x y : FilterMatrixCoronaAlgebra X l) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x y

/-- The quotient map from bounded sequences to the algebraic corona at `l`. -/
def filterMatrixCoronaMk :
    BoundedMatrixSequence X →+* FilterMatrixCoronaAlgebra X l :=
  Ideal.Quotient.mk (nullMatrixSequenceIdeal X l)

@[simp] theorem filterMatrixCoronaMk_apply (a : BoundedMatrixSequence X) :
    filterMatrixCoronaMk X l a =
      Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a := rfl

theorem filterMatrixCoronaMk_eq_zero_iff (a : BoundedMatrixSequence X) :
    filterMatrixCoronaMk X l a = 0 ↔ IsNullMatrixSequence X l a := by
  change Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-! ## The cofinite corona, behind an opaque interface

`FilterMatrixCoronaAlgebra` above remains reducible while its quotient norm
and operations are constructed.  Exposing that raw abbreviation directly to
downstream typeclass search makes Lean repeatedly unfold the noncommutative
ideal quotient.  The following definition is an opaque type synonym with the
same elements and explicitly transported structures.  It is the public
C-star-algebra object used by the unitary-corona correspondence, and it is the
cofinite instance -- the `ℓ∞/c₀` corona. -/

/-- The genuine norm-matrix C-star corona at the cofinite filter, exposed
behind an opaque boundary so its intended structures elaborate without
unfolding the ideal quotient. -/
def NormMatrixCStarCorona := FilterMatrixCoronaAlgebra X cofinite

noncomputable instance normMatrixCStarCoronaNormedRing :
    NormedRing (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraNormedRing X cofinite

noncomputable instance normMatrixCStarCoronaCompleteSpace :
    CompleteSpace (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraCompleteSpace X cofinite

noncomputable instance normMatrixCStarCoronaStarRing :
    StarRing (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraStarRing X cofinite

noncomputable instance normMatrixCStarCoronaNormedStarGroup :
    NormedStarGroup (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraNormedStarGroup X cofinite

noncomputable instance normMatrixCStarCoronaCStarRing :
    CStarRing (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraCStarRing X cofinite

noncomputable instance normMatrixCStarCoronaAlgebra :
    Algebra ℂ (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact Ideal.Quotient.algebra ℂ

noncomputable instance normMatrixCStarCoronaNormedAlgebra :
    NormedAlgebra ℂ (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraNormedAlgebra X cofinite

noncomputable instance normMatrixCStarCoronaStarModule :
    StarModule ℂ (NormMatrixCStarCorona X) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaAlgebraStarModule X cofinite

/-- The public quotient carries mathlib's bundled unital complex
C-star-algebra structure.  Its parent structures are the explicit quotient
structures constructed above. -/
noncomputable instance normMatrixCStarCoronaCStarAlgebra :
    CStarAlgebra (NormMatrixCStarCorona X) where
  toNormedRing := normMatrixCStarCoronaNormedRing X
  toStarRing := normMatrixCStarCoronaStarRing X
  toCompleteSpace := normMatrixCStarCoronaCompleteSpace X
  toCStarRing := normMatrixCStarCoronaCStarRing X
  toNormedAlgebra := normMatrixCStarCoronaNormedAlgebra X
  toStarModule := normMatrixCStarCoronaStarModule X

/-- The quotient homomorphism into the opaque C-star-corona interface. -/
def normMatrixCStarCoronaMk :
    BoundedMatrixSequence X →+* NormMatrixCStarCorona X := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaMk X cofinite

/-- The quotient map as a complex star-algebra homomorphism. -/
def normMatrixCStarCoronaQuotient :
    BoundedMatrixSequence X →⋆ₐ[ℂ] NormMatrixCStarCorona X where
  toFun := normMatrixCStarCoronaMk X
  map_one' := map_one (normMatrixCStarCoronaMk X)
  map_mul' := map_mul (normMatrixCStarCoronaMk X)
  map_zero' := map_zero (normMatrixCStarCoronaMk X)
  map_add' := map_add (normMatrixCStarCoronaMk X)
  commutes' z := by
    unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
    exact Ideal.Quotient.mk_algebraMap ℂ (nullMatrixSequenceIdeal X cofinite) z
  map_star' a := by
    unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
    exact (filterMatrixCorona_star_mk X cofinite a).symm

@[simp] theorem normMatrixCStarCorona_star_mk (a : BoundedMatrixSequence X) :
    star (normMatrixCStarCoronaMk X a) =
      normMatrixCStarCoronaMk X (star a) := by
  unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact filterMatrixCorona_star_mk X cofinite a

theorem normMatrixCStarCoronaMk_eq_zero_iff (a : BoundedMatrixSequence X) :
    normMatrixCStarCoronaMk X a = 0 ↔ IsNullMatrixSequence X cofinite a := by
  unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact filterMatrixCoronaMk_eq_zero_iff X cofinite a

/-- A cofinite norm-matrix corona with nonempty coordinate spaces is
nontrivial.  The constant identity sequence cannot converge to zero in
operator norm. -/
noncomputable instance normMatrixCStarCoronaNontrivial :
    Nontrivial (NormMatrixCStarCorona X) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro hone
  have hmk : normMatrixCStarCoronaMk X (1 : BoundedMatrixSequence X) = 0 := by
    rw [map_one, hone]
  have hnull : IsNullMatrixSequence X cofinite
      (1 : BoundedMatrixSequence X) :=
    (normMatrixCStarCoronaMk_eq_zero_iff X _).mp hmk
  have hnorm :
      (fun n ↦ ‖((1 : BoundedMatrixSequence X) n)‖) =
        fun _ : ℕ ↦ (1 : ℝ) := by
    funext n
    exact norm_one
  rw [IsNullMatrixSequence, hnorm] at hnull
  have honezero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hnull
  norm_num at honezero

/-- Every element of the opaque corona has a bounded matrix-sequence lift. -/
theorem normMatrixCStarCoronaMk_surjective :
    Function.Surjective (normMatrixCStarCoronaMk X) := by
  unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact Ideal.Quotient.mk_surjective

end

end GroupApproximation
