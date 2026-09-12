import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polar lifting over arbitrary unital C-star blocks

The manuscript's Questions subsection asks whether the obstruction of
`thm:kazhdan-transport` survives when the matrix blocks `M_{d_n}(ℂ)` are
replaced "by other building blocks", and answers one half of that question
outright:

> Unitary lifting itself works for arbitrary unital coordinate algebras: if
> `u` is unitary in the quotient and `(x_n)` is any lift, then
> `‖x_n^*x_n - 1‖ → 0` and `‖x_nx_n^* - 1‖ → 0`, so `x_n` is invertible for
> all large `n` and the polar correction `u_n = x_n(x_n^*x_n)^{-1/2}` is
> unitary with `‖u_n - x_n‖ → 0`, with no real-rank-zero or semiprojectivity
> hypothesis in the sense of Loring.  The matrix-specific inputs are the
> Hilbert-space conjugation model and finiteness of the norm ultraproduct,
> not the lifting step.

This file proves exactly that sentence for an arbitrary sequence of unital
C-star algebras, at an arbitrary filter (the printed statement is the
`cofinite` case, where the denominator is the `c₀`-sum `⨁_n A_n`).
`printedUnitaryLifting` is the sentence as a single statement: the four
printed clauses, in the printed order, about the printed sequence
`u_n = x_n(x_n^*x_n)^{-1/2}`.

## What the matrix development does and does not supply

`Sofic/KazhdanCornerPolar` performs the correction for a single finite
matrix, in the eigenbasis of `CᴴC`, and `Analysis/NormMatrixCoronaUnitary`
assembles it into the surjectivity half of the unitary-corona equivalence.
Both are genuinely finite-dimensional: they are written through mathlib's
Hermitian spectral theorem.  Here the same correction is carried out by the
continuous functional calculus, which needs nothing beyond a unital
C-star algebra, and the scalar estimate `|t^{-1/2} - 1| ≤ 2δ` on
`[1-δ, 1+δ]` for `δ ≤ 1/2` is the *same* estimate — it is a statement about
real numbers and is reproved here only so that this file does not import the
group-theoretic chain under `Sofic/KazhdanCornerMatrices`.

## Why no quotient norm is constructed

The lifting statement is algebraic: a unitary of `(∏_nA_n)/(⨁_nA_n)` is an
element `q` of the ring quotient with `q^*q = qq^* = 1`, and `q^*q = 1` says
precisely that `star x * x - 1` lies in the null ideal, i.e. that
`‖x_n^*x_n - 1‖ → 0`.  Nothing below needs the quotient to carry a
C-star norm, and that is the manuscript's point: the lifting is not where
the structure of the blocks enters.  (`Analysis/NormMatrixCorona` builds the
quotient C-star norm for the matrix blocks, where it *is* needed, as the
limsup of the coordinate norms.)

## The one hypothesis that is not printed

`[∀ n, Nontrivial (A n)]`.  The zero algebra is unital, but the pinned
library builds the *unital* ring structure on `lp A ∞` only under
`NormOneClass` of every block, which for a C-star algebra is exactly
nontriviality; without it `∏_nA_n` is not a unital normed ring in mathlib's
sense.  This excludes no unitary group: the zero algebra has none.
-/

namespace GroupApproximation
namespace PolarLiftingGeneralCStar

open Filter
open scoped ENNReal

noncomputable section

/-! ## The scalar estimate

For `t` within `δ ≤ 1/2` of `1` the reciprocal square root is within `2δ`
of `1`.  This is the estimate behind the printed constant in
`‖u_n - x_n‖ ≤ 2‖x_n‖ ‖x_n^*x_n - 1‖`; it is the real-variable content of
`KazhdanCornerMatrices.abs_inv_sqrt_sub_one_le_two_mul`, restated here to
keep this file's imports inside the analysis layer. -/

private theorem abs_inv_sqrt_sub_one_le_two_mul {lambda delta : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : |lambda - 1| ≤ delta) :
    |(Real.sqrt lambda)⁻¹ - 1| ≤ 2 * delta := by
  let r := Real.sqrt lambda
  have hr0 : 0 ≤ r := Real.sqrt_nonneg lambda
  have hrsq : r ^ 2 = lambda := Real.sq_sqrt hlambda.le
  have hlower : 1 / 2 ≤ lambda := by
    have := (neg_le_of_abs_le hclose)
    linarith
  have hrhalf : 1 / 2 ≤ r := by
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hrhalf
  rcases le_total r 1 with hrle | honele
  · have hnumer : 0 ≤ 1 - r := sub_nonneg.mpr hrle
    have hsmall : 1 - r ≤ delta := by
      have hbelow := neg_le_of_abs_le hclose
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hrle)]
    rw [show r⁻¹ - 1 = (1 - r) / r by field_simp]
    rw [abs_of_nonneg (div_nonneg hnumer hr0), div_le_iff₀ hrpos]
    nlinarith
  · have hnonpos : r⁻¹ - 1 ≤ 0 := by
      exact sub_nonpos.mpr ((inv_le_one₀ hrpos).2 honele)
    have hsmall : r - 1 ≤ delta := by
      have hupper := le_of_abs_le hclose
      nlinarith
    rw [abs_of_nonpos hnonpos]
    rw [show -(r⁻¹ - 1) = (r - 1) / r by field_simp; ring]
    rw [div_le_iff₀ hrpos]
    nlinarith

/-! ## Polar correction in a single unital C-star algebra -/

section Pointwise

variable {A : Type*} [CStarAlgebra A]

/-- The printed correction symbol `t ↦ t^{-1/2}`. -/
def invSqrt : ℝ → ℝ := fun t ↦ (Real.sqrt t)⁻¹

@[simp] theorem invSqrt_apply (t : ℝ) : invSqrt t = (Real.sqrt t)⁻¹ := rfl

/-- `(x^*x)^{-1/2}`, defined by the continuous functional calculus of the
self-adjoint element `x^*x`.  No finite dimensionality, real rank zero or
semiprojectivity is involved. -/
noncomputable def polarInvSqrt (x : A) : A := cfc invSqrt (star x * x)

/-- The printed polar correction `u = x(x^*x)^{-1/2}`. -/
noncomputable def polarUnitary (x : A) : A := x * polarInvSqrt x

/-- Every real spectral value of `a` is within `‖a - 1‖` of `1`. -/
theorem abs_sub_one_le_of_mem_spectrum {a : A} {t : ℝ} (ht : t ∈ spectrum ℝ a) :
    |t - 1| ≤ ‖a - 1‖ := by
  obtain (hA | hA) := subsingleton_or_nontrivial A
  · rw [spectrum.of_subsingleton] at ht
    exact absurd ht (Set.notMem_empty t)
  · have hmem : t - 1 ∈ spectrum ℝ (a - algebraMap ℝ A 1) := by
      rw [← spectrum.sub_singleton_eq]
      exact Set.sub_mem_sub ht rfl
    rw [map_one] at hmem
    simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hmem

/-- Under the printed `1/2` hypothesis the Gram element has strictly positive
spectrum, so `t^{-1/2}` is continuous where it is applied. -/
theorem spectrum_pos_of_norm_gram_le {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ spectrum ℝ (star x * x)) : 0 < t := by
  have h : |t - 1| ≤ 1 / 2 := (abs_sub_one_le_of_mem_spectrum ht).trans hx
  have hlow := neg_le_of_abs_le h
  linarith

theorem continuousOn_invSqrt_spectrum {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    ContinuousOn invSqrt (spectrum ℝ (star x * x)) := by
  have h : ContinuousOn (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (spectrum ℝ (star x * x)) :=
    Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦
      (Real.sqrt_pos.mpr (spectrum_pos_of_norm_gram_le hx ht)).ne'
  exact h

theorem polarInvSqrt_isSelfAdjoint (x : A) : IsSelfAdjoint (polarInvSqrt x) :=
  cfc_predicate invSqrt (star x * x)

theorem isUnit_polarInvSqrt {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    IsUnit (polarInvSqrt x) := by
  have hsa : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have hcont := continuousOn_invSqrt_spectrum hx
  have h : IsUnit (cfc invSqrt (star x * x)) := by
    rw [isUnit_cfc_iff invSqrt (star x * x) hcont hsa]
    intro t ht
    exact inv_ne_zero (Real.sqrt_pos.mpr (spectrum_pos_of_norm_gram_le hx ht)).ne'
  exact h

/-- **Eventual invertibility, at a single block.**  A Gram defect strictly
below `1` on both sides makes `x` invertible.  This is the printed step "so
`x_n` is invertible for all large `n`"; it is the Neumann series, not
finite dimensionality. -/
theorem isUnit_of_norm_gram_lt {x : A} (h1 : ‖star x * x - 1‖ < 1)
    (h2 : ‖x * star x - 1‖ < 1) : IsUnit x := by
  have hg1 : IsUnit (star x * x) := by
    have hn : ‖(1 : A) - star x * x‖ < 1 := by
      rw [← neg_sub, norm_neg]; exact h1
    have h := isUnit_one_sub_of_norm_lt_one hn
    rwa [sub_sub_cancel] at h
  have hg2 : IsUnit (x * star x) := by
    have hn : ‖(1 : A) - x * star x‖ < 1 := by
      rw [← neg_sub, norm_neg]; exact h2
    have h := isUnit_one_sub_of_norm_lt_one hn
    rwa [sub_sub_cancel] at h
  rw [isUnit_iff_exists_and_exists]
  refine ⟨⟨star x * Ring.inverse (x * star x), ?_⟩,
          ⟨Ring.inverse (star x * x) * star x, ?_⟩⟩
  · rw [← mul_assoc]
    exact Ring.mul_inverse_cancel _ hg2
  · rw [mul_assoc]
    exact Ring.inverse_mul_cancel _ hg1

/-- The defining identity of the correction: `(x^*x)^{-1/2}(x^*x)(x^*x)^{-1/2} = 1`. -/
theorem polarInvSqrt_gram_polarInvSqrt {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    polarInvSqrt x * (star x * x) * polarInvSqrt x = 1 := by
  have hsa : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have hcont := continuousOn_invSqrt_spectrum hx
  have hid : ContinuousOn (fun t : ℝ ↦ t) (spectrum ℝ (star x * x)) :=
    continuousOn_id' _
  have h1 : cfc (fun t : ℝ ↦ invSqrt t * t) (star x * x)
      = cfc invSqrt (star x * x) * cfc (fun t : ℝ ↦ t) (star x * x) :=
    cfc_mul invSqrt (fun t : ℝ ↦ t) (star x * x) hcont hid
  rw [cfc_id' ℝ (star x * x) hsa] at h1
  have h2 : cfc (fun t : ℝ ↦ invSqrt t * t * invSqrt t) (star x * x)
      = cfc (fun t : ℝ ↦ invSqrt t * t) (star x * x) * cfc invSqrt (star x * x) :=
    cfc_mul (fun t : ℝ ↦ invSqrt t * t) invSqrt (star x * x) (hcont.mul hid) hcont
  have h3 : cfc (fun t : ℝ ↦ invSqrt t * t * invSqrt t) (star x * x)
      = cfc (fun _ : ℝ ↦ (1 : ℝ)) (star x * x) := by
    apply cfc_congr
    intro t ht
    have htpos : 0 < t := spectrum_pos_of_norm_gram_le hx ht
    have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
    show (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹ = 1
    have hrw : (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹
        = t * ((Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹) := by ring
    rw [hrw, ← mul_inv, hs, mul_inv_cancel₀ htpos.ne']
  show cfc invSqrt (star x * x) * (star x * x) * cfc invSqrt (star x * x) = 1
  rw [← h1, ← h2, h3]
  exact cfc_const_one ℝ (star x * x) hsa

/-- **The polar correction is unitary.**  Exactly the printed hypotheses: the
two Gram defects are at most `1/2`. -/
theorem polarUnitary_mem_unitary {x : A} (h1 : ‖star x * x - 1‖ ≤ 1 / 2)
    (h2 : ‖x * star x - 1‖ ≤ 1 / 2) : polarUnitary x ∈ unitary A := by
  have hxu : IsUnit x := isUnit_of_norm_gram_lt (by linarith) (by linarith)
  have hcu : IsUnit (polarInvSqrt x) := isUnit_polarInvSqrt h1
  have hu : IsUnit (polarUnitary x) := hxu.mul hcu
  have hsa : IsSelfAdjoint (polarInvSqrt x) := polarInvSqrt_isSelfAdjoint x
  refine hu.mem_unitary_of_star_mul_self ?_
  calc star (polarUnitary x) * polarUnitary x
      = star (x * polarInvSqrt x) * (x * polarInvSqrt x) := rfl
    _ = polarInvSqrt x * (star x * x) * polarInvSqrt x := by
        rw [star_mul, hsa.star_eq]
        simp only [mul_assoc]
    _ = 1 := polarInvSqrt_gram_polarInvSqrt h1

/-- The correction moves the Gram element's inverse square root by at most
twice the Gram defect. -/
theorem norm_polarInvSqrt_sub_one_le {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    ‖polarInvSqrt x - 1‖ ≤ 2 * ‖star x * x - 1‖ := by
  have hsa : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have hcont := continuousOn_invSqrt_spectrum hx
  have hsub : cfc (fun t : ℝ ↦ invSqrt t - 1) (star x * x)
      = cfc invSqrt (star x * x) - cfc (fun _ : ℝ ↦ (1 : ℝ)) (star x * x) :=
    cfc_sub invSqrt (fun _ : ℝ ↦ (1 : ℝ)) (star x * x) hcont continuousOn_const
  rw [cfc_const_one ℝ (star x * x) hsa] at hsub
  have hgoal : polarInvSqrt x - 1 = cfc (fun t : ℝ ↦ invSqrt t - 1) (star x * x) :=
    hsub.symm
  rw [hgoal]
  refine norm_cfc_le (by positivity) ?_
  intro t ht
  have htpos : 0 < t := spectrum_pos_of_norm_gram_le hx ht
  have habs : |t - 1| ≤ ‖star x * x - 1‖ := abs_sub_one_le_of_mem_spectrum ht
  have hbound := abs_inv_sqrt_sub_one_le_two_mul htpos (norm_nonneg _) hx habs
  simpa only [Real.norm_eq_abs, invSqrt_apply] using hbound

/-- **The printed estimate**, with the printed constant:
`‖u - x‖ ≤ 2‖x‖ ‖x^*x - 1‖`. -/
theorem norm_polarUnitary_sub_le {x : A} (hx : ‖star x * x - 1‖ ≤ 1 / 2) :
    ‖polarUnitary x - x‖ ≤ 2 * ‖x‖ * ‖star x * x - 1‖ := by
  have hrw : polarUnitary x - x = x * (polarInvSqrt x - 1) := by
    show x * polarInvSqrt x - x = x * (polarInvSqrt x - 1)
    rw [mul_sub, mul_one]
  rw [hrw]
  calc ‖x * (polarInvSqrt x - 1)‖ ≤ ‖x‖ * ‖polarInvSqrt x - 1‖ := norm_mul_le _ _
    _ ≤ ‖x‖ * (2 * ‖star x * x - 1‖) :=
        mul_le_mul_of_nonneg_left (norm_polarInvSqrt_sub_one_le hx) (norm_nonneg _)
    _ = 2 * ‖x‖ * ‖star x * x - 1‖ := by ring

end Pointwise

/-! ## The product and its null ideal

`BoundedCStarSequence A` is the bounded product `∏_n A_n`, mathlib's
dependent `ℓ∞` space, already a C-star algebra; the denominator is the
genuine two-sided star-stable ideal of sequences whose norms vanish along a
filter `l`.  At `l = cofinite` the ideal is the `c₀`-sum `⨁_n A_n` of the
printed statement. -/

section Corona

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]

/-- The bounded C-star product `∏_n A_n`. -/
abbrev BoundedCStarSequence := lp A ∞

theorem boundedCStarSequence_coord_norm_le (a : BoundedCStarSequence A) (n : ℕ) :
    ‖a n‖ ≤ ‖a‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero a n

variable (l : Filter ℕ)

/-- A bounded sequence is null along `l` when its coordinate norms tend to
zero along `l`. -/
def IsNullCStarSequence (a : BoundedCStarSequence A) : Prop :=
  Tendsto (fun n ↦ ‖a n‖) l (nhds 0)

namespace IsNullCStarSequence

theorem zero : IsNullCStarSequence A l 0 := by
  rw [IsNullCStarSequence]
  refine tendsto_const_nhds.congr fun n ↦ ?_
  simp

theorem add {a b : BoundedCStarSequence A} (ha : IsNullCStarSequence A l a)
    (hb : IsNullCStarSequence A l b) : IsNullCStarSequence A l (a + b) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a + b) n))
  · filter_upwards with n
    exact norm_add_le _ _
  · simpa only [add_zero] using Filter.Tendsto.add ha hb

theorem mul_left (b : BoundedCStarSequence A) {a : BoundedCStarSequence A}
    (ha : IsNullCStarSequence A l a) : IsNullCStarSequence A l (b * a) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((b * a) n))
  · filter_upwards with n
    exact (norm_mul_le (b n) (a n)).trans
      (mul_le_mul_of_nonneg_right (boundedCStarSequence_coord_norm_le A b n)
        (norm_nonneg _))
  · simpa only [mul_zero] using tendsto_const_nhds.mul ha

theorem mul_right {a : BoundedCStarSequence A} (ha : IsNullCStarSequence A l a)
    (b : BoundedCStarSequence A) : IsNullCStarSequence A l (a * b) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg ((a * b) n))
  · filter_upwards with n
    exact (norm_mul_le (a n) (b n)).trans
      (mul_le_mul_of_nonneg_left (boundedCStarSequence_coord_norm_le A b n)
        (norm_nonneg _))
  · simpa only [zero_mul] using ha.mul tendsto_const_nhds

theorem star {a : BoundedCStarSequence A} (ha : IsNullCStarSequence A l a) :
    IsNullCStarSequence A l (star a) := by
  simpa [IsNullCStarSequence, lp.star_apply] using ha

end IsNullCStarSequence

/-! ## The corrected sequence -/

/-- The indices where the printed polar correction applies.  This is an
`abbrev` so that the `Decidable` instance used by `polarLift` below is the
one instance search finds for a conjunction of real inequalities, and the
`if_pos`/`if_neg` unfoldings elaborate against that same instance. -/
abbrev PolarGood (x : BoundedCStarSequence A) (n : ℕ) : Prop :=
  ‖star (x n) * x n - 1‖ ≤ 1 / 2 ∧ ‖x n * star (x n) - 1‖ ≤ 1 / 2

/-- The polar-corrected sequence: the printed correction where it applies,
and the identity at the remaining indices ("set `u_n = 1` at the finitely
many remaining indices", which for a general filter means off a member of
`l`). -/
noncomputable def polarLift (x : BoundedCStarSequence A) (n : ℕ) : A n :=
  if PolarGood A x n then polarUnitary (x n) else 1

theorem polarLift_of_good {x : BoundedCStarSequence A} {n : ℕ}
    (h : PolarGood A x n) : polarLift A x n = polarUnitary (x n) :=
  if_pos h

theorem polarLift_of_not_good {x : BoundedCStarSequence A} {n : ℕ}
    (h : ¬ PolarGood A x n) : polarLift A x n = 1 :=
  if_neg h

theorem polarLift_mem_unitary (x : BoundedCStarSequence A) (n : ℕ) :
    polarLift A x n ∈ unitary (A n) := by
  by_cases hn : PolarGood A x n
  · rw [polarLift_of_good A hn]
    exact polarUnitary_mem_unitary hn.1 hn.2
  · rw [polarLift_of_not_good A hn]
    exact (unitary (A n)).one_mem

/-! ## The unital region

Everything from here on needs the *unital* ring structure on `∏_nA_n`, and
mathlib builds that only under `NormOneClass` of every block -- which for a
C-star algebra is exactly nontriviality.  Declaring the binder here rather
than at the top of the section is what keeps it used by every declaration
that carries it: adding `omit` above instead only moves the unused frontier
onto the callers. -/

variable [∀ n, Nontrivial (A n)]

/-- The two-sided ideal `⨁_l A_n` of sequences null along `l`.  At
`l = cofinite` this is the `c₀`-sum `⨁_n A_n`. -/
def nullCStarSequenceIdeal : Ideal (BoundedCStarSequence A) where
  carrier := {a | IsNullCStarSequence A l a}
  zero_mem' := IsNullCStarSequence.zero A l
  add_mem' := IsNullCStarSequence.add A l
  smul_mem' := fun b _ ha ↦ IsNullCStarSequence.mul_left A l b ha

instance nullCStarSequenceIdeal_isTwoSided :
    (nullCStarSequenceIdeal A l).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ IsNullCStarSequence.mul_right A l ha b

theorem mem_nullCStarSequenceIdeal_iff (a : BoundedCStarSequence A) :
    a ∈ nullCStarSequenceIdeal A l ↔ IsNullCStarSequence A l a := Iff.rfl

theorem nullCStarSequenceIdeal_star_mem {a : BoundedCStarSequence A}
    (ha : a ∈ nullCStarSequenceIdeal A l) :
    star a ∈ nullCStarSequenceIdeal A l :=
  IsNullCStarSequence.star A l ha

/-- The corona `(∏_n A_n)/(⨁_l A_n)`.  At `l = cofinite` this is the
printed `(∏_nA_n)/(⨁_nA_n)`. -/
abbrev CStarProductCorona := BoundedCStarSequence A ⧸ nullCStarSequenceIdeal A l

private def boundedCStarSequenceStarHom :
    BoundedCStarSequence A →+ CStarProductCorona A l :=
  (Ideal.Quotient.mk (nullCStarSequenceIdeal A l)).toAddMonoidHom.comp
    starAddEquiv.toAddMonoidHom

private theorem nullCStarSequenceIdeal_le_star_ker :
    (nullCStarSequenceIdeal A l).toAddSubgroup ≤
      (boundedCStarSequenceStarHom A l).ker := by
  intro a ha
  change Ideal.Quotient.mk (nullCStarSequenceIdeal A l) (star a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact nullCStarSequenceIdeal_star_mem A l ha

/-- Coordinatewise adjoint descends to the corona. -/
noncomputable instance coronaStar : Star (CStarProductCorona A l) where
  star := QuotientAddGroup.lift
    (nullCStarSequenceIdeal A l).toAddSubgroup
    (boundedCStarSequenceStarHom A l)
    (nullCStarSequenceIdeal_le_star_ker A l)

@[simp] theorem corona_star_mk (a : BoundedCStarSequence A) :
    star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a) =
      Ideal.Quotient.mk (nullCStarSequenceIdeal A l) (star a) :=
  QuotientAddGroup.lift_mk _ _ _

noncomputable instance coronaInvolutiveStar :
    InvolutiveStar (CStarProductCorona A l) where
  star_involutive x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change star (star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a)) =
        Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a
      rw [corona_star_mk, corona_star_mk, star_star]

noncomputable instance coronaStarRing : StarRing (CStarProductCorona A l) where
  star_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) (a + b)) =
          star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a) +
            star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) b)
        rw [corona_star_mk, corona_star_mk, corona_star_mk, star_add]
        rfl
  star_mul x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) (a * b)) =
          star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) b) *
            star (Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a)
        rw [corona_star_mk, corona_star_mk, corona_star_mk]
        rw [show star (a * b) = star b * star a from StarMul.star_mul a b]
        rfl

/-! ## Coordinates of the two Gram defects -/

@[simp] theorem gram_apply (x : BoundedCStarSequence A) (n : ℕ) :
    (star x * x - 1) n = star (x n) * x n - 1 := rfl

@[simp] theorem gram'_apply (x : BoundedCStarSequence A) (n : ℕ) :
    (x * star x - 1) n = x n * star (x n) - 1 := rfl

/-- The corrected sequence is bounded, since every coordinate is unitary. -/
noncomputable def polarLiftSeq (x : BoundedCStarSequence A) :
    BoundedCStarSequence A :=
  ⟨polarLift A x, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq
      (CStarRing.norm_of_mem_unitary (polarLift_mem_unitary A x n))⟩⟩

@[simp] theorem polarLiftSeq_apply (x : BoundedCStarSequence A) (n : ℕ) :
    polarLiftSeq A x n = polarLift A x n := rfl

theorem polarLiftSeq_mem_unitary (x : BoundedCStarSequence A) (n : ℕ) :
    polarLiftSeq A x n ∈ unitary (A n) :=
  polarLift_mem_unitary A x n

/-! ## The lifting -/

/-- **The printed first step.**  Any lift of a unitary of the corona has both
Gram defects vanishing along the filter. -/
theorem isNull_gram_of_mem_unitary (x : BoundedCStarSequence A)
    (hq : Ideal.Quotient.mk (nullCStarSequenceIdeal A l) x ∈
      unitary (CStarProductCorona A l)) :
    IsNullCStarSequence A l (star x * x - 1) ∧
      IsNullCStarSequence A l (x * star x - 1) := by
  constructor
  · have hs := Unitary.star_mul_self_of_mem hq
    rw [corona_star_mk] at hs
    have hzero : Ideal.Quotient.mk (nullCStarSequenceIdeal A l)
        (star x * x - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hs, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  · have hs := Unitary.mul_star_self_of_mem hq
    rw [corona_star_mk] at hs
    have hzero : Ideal.Quotient.mk (nullCStarSequenceIdeal A l)
        (x * star x - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hs, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero

theorem eventually_polarGood (x : BoundedCStarSequence A)
    (h1 : IsNullCStarSequence A l (star x * x - 1))
    (h2 : IsNullCStarSequence A l (x * star x - 1)) :
    ∀ᶠ n in l, PolarGood A x n := by
  have e1 : ∀ᶠ n in l, ‖(star x * x - 1) n‖ ≤ (1 : ℝ) / 2 := by
    have hd := (Metric.tendsto_nhds.mp h1) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  have e2 : ∀ᶠ n in l, ‖(x * star x - 1) n‖ ≤ (1 : ℝ) / 2 := by
    have hd := (Metric.tendsto_nhds.mp h2) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  filter_upwards [e1, e2] with n hn1 hn2
  refine ⟨?_, ?_⟩
  · have h : ‖(star x * x - 1) n‖ ≤ (1 : ℝ) / 2 := hn1
    rw [gram_apply] at h
    exact h
  · have h : ‖(x * star x - 1) n‖ ≤ (1 : ℝ) / 2 := hn2
    rw [gram'_apply] at h
    exact h

/-- **"so `x_n` is invertible for all large `n`".**  Every lift of a unitary
of the corona is invertible along the filter. -/
theorem eventually_isUnit_of_mem_unitary (x : BoundedCStarSequence A)
    (hq : Ideal.Quotient.mk (nullCStarSequenceIdeal A l) x ∈
      unitary (CStarProductCorona A l)) :
    ∀ᶠ n in l, IsUnit (x n) := by
  obtain ⟨h1, h2⟩ := isNull_gram_of_mem_unitary A l x hq
  filter_upwards [eventually_polarGood A l x h1 h2] with n hn
  have hn1 := hn.1
  have hn2 := hn.2
  exact isUnit_of_norm_gram_lt (by linarith) (by linarith)

/-- **"with `‖u_n - x_n‖ → 0`".**  The polar correction of any lift of a
unitary converges to that lift in norm, coordinatewise along the filter. -/
theorem tendsto_norm_polarLift_sub (x : BoundedCStarSequence A)
    (h1 : IsNullCStarSequence A l (star x * x - 1))
    (h2 : IsNullCStarSequence A l (x * star x - 1)) :
    Tendsto (fun n ↦ ‖polarLiftSeq A x n - x n‖) l (nhds 0) := by
  have hgood := eventually_polarGood A l x h1 h2
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ norm_nonneg (polarLiftSeq A x n - x n))
  · filter_upwards [hgood] with n hn
    show ‖polarLiftSeq A x n - x n‖ ≤ 2 * ‖x‖ * ‖(star x * x - 1) n‖
    have hstep : ‖polarLift A x n - x n‖
        ≤ 2 * ‖x n‖ * ‖star (x n) * x n - 1‖ := by
      rw [polarLift_of_good A hn]
      exact norm_polarUnitary_sub_le hn.1
    calc ‖polarLiftSeq A x n - x n‖ = ‖polarLift A x n - x n‖ := rfl
      _ ≤ 2 * ‖x n‖ * ‖star (x n) * x n - 1‖ := hstep
      _ ≤ 2 * ‖x‖ * ‖(star x * x - 1) n‖ := by
          rw [gram_apply]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (boundedCStarSequence_coord_norm_le A x n) (by norm_num)
  · have h1' : Tendsto (fun n ↦ ‖(star x * x - 1) n‖) l (nhds 0) := h1
    simpa using h1'.const_mul (2 * ‖x‖)

theorem isNull_polarLiftSeq_sub (x : BoundedCStarSequence A)
    (h1 : IsNullCStarSequence A l (star x * x - 1))
    (h2 : IsNullCStarSequence A l (x * star x - 1)) :
    IsNullCStarSequence A l (polarLiftSeq A x - x) :=
  tendsto_norm_polarLift_sub A l x h1 h2

/-- **The lifting, over arbitrary unital blocks.**  Every unitary of the
corona `(∏_nA_n)/(⨁_lA_n)` has a coordinatewise-unitary lift.  No real rank
zero, no semiprojectivity, no finite dimensionality: the argument is the
printed polar correction. -/
theorem exists_unitary_lift (q : CStarProductCorona A l)
    (hq : q ∈ unitary (CStarProductCorona A l)) :
    ∃ u : BoundedCStarSequence A, (∀ n, u n ∈ unitary (A n)) ∧
      Ideal.Quotient.mk (nullCStarSequenceIdeal A l) u = q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨h1, h2⟩ := isNull_gram_of_mem_unitary A l x hq
  refine ⟨polarLiftSeq A x, polarLiftSeq_mem_unitary A x, ?_⟩
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact isNull_polarLiftSeq_sub A l x h1 h2

/-- **The printed sentence, as one statement.**  For arbitrary unital
coordinate algebras: if `u` is unitary in the quotient and `(x_n)` is any
lift, then

* `‖x_n^*x_n - 1‖ → 0` and `‖x_nx_n^* - 1‖ → 0`;
* `x_n` is invertible for all large `n`;
* the polar correction `u_n = x_n(x_n^*x_n)^{-1/2}` is unitary;
* `‖u_n - x_n‖ → 0`, and `(u_n)` lifts the same unitary `u`.

No real-rank-zero and no semiprojectivity hypothesis occurs anywhere in the
statement or in its proof. -/
theorem printedUnitaryLifting (x : BoundedCStarSequence A)
    (hq : Ideal.Quotient.mk (nullCStarSequenceIdeal A l) x ∈
      unitary (CStarProductCorona A l)) :
    Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) l (nhds 0) ∧
      Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) l (nhds 0) ∧
      (∀ᶠ n in l, IsUnit (x n)) ∧
      (∀ n, polarLiftSeq A x n ∈ unitary (A n)) ∧
      Tendsto (fun n ↦ ‖polarLiftSeq A x n - x n‖) l (nhds 0) ∧
      Ideal.Quotient.mk (nullCStarSequenceIdeal A l) (polarLiftSeq A x) =
        Ideal.Quotient.mk (nullCStarSequenceIdeal A l) x := by
  obtain ⟨h1, h2⟩ := isNull_gram_of_mem_unitary A l x hq
  refine ⟨?_, ?_, eventually_isUnit_of_mem_unitary A l x hq,
    polarLiftSeq_mem_unitary A x, tendsto_norm_polarLift_sub A l x h1 h2, ?_⟩
  · have h1' : Tendsto (fun n ↦ ‖(star x * x - 1) n‖) l (nhds 0) := h1
    simpa only [gram_apply] using h1'
  · have h2' : Tendsto (fun n ↦ ‖(x * star x - 1) n‖) l (nhds 0) := h2
    simpa only [gram'_apply] using h2'
  · rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact isNull_polarLiftSeq_sub A l x h1 h2

end Corona

/-- **The printed statement.**  For arbitrary unital C-star algebras `A_n`,
every unitary of `(∏_nA_n)/(⨁_nA_n)` lifts to a sequence of unitaries.  This
is the manuscript's answer, in its Questions subsection, to the half of the
"other building blocks" question concerning `lem:lift`: the lifting is *not*
where the matrix structure enters. -/
theorem exists_unitary_lift_cofinite (A : ℕ → Type*) [∀ n, CStarAlgebra (A n)]
    [∀ n, Nontrivial (A n)] (q : CStarProductCorona A cofinite)
    (hq : q ∈ unitary (CStarProductCorona A cofinite)) :
    ∃ u : BoundedCStarSequence A, (∀ n, u n ∈ unitary (A n)) ∧
      Ideal.Quotient.mk (nullCStarSequenceIdeal A cofinite) u = q :=
  exists_unitary_lift A cofinite q hq

/-- **The printed sentence at the printed algebra** `(∏_nA_n)/(⨁_nA_n)`. -/
theorem printedUnitaryLifting_cofinite (A : ℕ → Type*)
    [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
    (x : BoundedCStarSequence A)
    (hq : Ideal.Quotient.mk (nullCStarSequenceIdeal A cofinite) x ∈
      unitary (CStarProductCorona A cofinite)) :
    Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) ∧
      Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) cofinite (nhds 0) ∧
      (∀ᶠ n in cofinite, IsUnit (x n)) ∧
      (∀ n, polarLiftSeq A x n ∈ unitary (A n)) ∧
      Tendsto (fun n ↦ ‖polarLiftSeq A x n - x n‖) cofinite (nhds 0) ∧
      Ideal.Quotient.mk (nullCStarSequenceIdeal A cofinite) (polarLiftSeq A x) =
        Ideal.Quotient.mk (nullCStarSequenceIdeal A cofinite) x :=
  printedUnitaryLifting A cofinite x hq

end

end PolarLiftingGeneralCStar
end GroupApproximation
