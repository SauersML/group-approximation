import GroupApproximation.Analysis.CStarPositiveOrder
import GroupApproximation.Analysis.CStarFiniteRank

/-!
# Cauchy--Schwarz, and the norm of a Hilbert C⋆-module

`Analysis.CStarHilbertModule` builds Hilbert C⋆-modules and
`Analysis.CStarFiniteRank` the finite-rank ideal, and both stop at the same
wall: the compact operators `𝓚(E)` are the **closure** of the finite-rank
operators, and there was no norm to close in.  A Hilbert module has one ---
`‖x‖ = ‖⟨x,x⟩‖^{1/2}` --- but that it *is* a norm is the `B`-valued
Cauchy--Schwarz inequality, whose proof is an order argument in `B`.
`Analysis.CStarPositiveOrder` supplies the order; this file spends it.

## What is proved

Everything, unconditionally, for an arbitrary bundled `E : CStarModule B`.

* `inner_mul_inner_swap_le` --- **the C⋆-valued Cauchy--Schwarz inequality**
  `⟨y,x⟩⟨x,y⟩ ≤ ‖⟨x,x⟩‖ • ⟨y,y⟩`.  Note the shape: the bound is *not*
  `⟨x,x⟩`-conjugated but scaled by its **norm**.  That asymmetry is forced ---
  `⟨y,x⟩⟨x,y⟩ ≤ ⟨x,x⟩⟨y,y⟩` is not even a statement about positive elements,
  since a product of positives need not be positive --- and it is what makes
  the resulting norm submultiplicative over the action rather than
  multiplicative.
* `norm_inner_le` --- the scalar form `‖⟨x,y⟩‖ ≤ ‖x‖‖y‖`;
* `norm_add_le`, `norm_smul`, `norm_eq_zero_iff` --- so `‖·‖` is a norm;
* `norm_act_le` --- `‖x·b‖ ≤ ‖x‖‖b‖`, the estimate that makes rank-one
  operators bounded, hence the one the operator norm on `𝓛(E)` is built from;
* `toNormedAddCommGroup` --- the four facts packaged, so that the carrier of a
  Hilbert module may be regarded as a normed space whenever that is wanted;
* `selfModule_norm` --- on `B` itself the module norm *is* the C⋆-norm, which
  is what lets a general module estimate be read back as an estimate in `B`.

## The proof, and why it is written with an explicit test vector

The classical argument tests positivity of `⟨z,z⟩` at `z = x·b - ‖⟨x,x⟩‖·y`
and then *chooses* `b = ⟨x,y⟩`.  Both steps are visible below:
`cauchySchwarzAux` is the inequality for an arbitrary `b`, and
`inner_mul_inner_swap_le` is its specialization.  Keeping them apart is not
decoration --- the auxiliary form is the one that generalizes to the
several-vector estimates the standard module `H_B` needs, and specializing
early would lose it.

The scalar `‖⟨x,x⟩‖` rather than `1` in the test vector is what makes the
final cancellation exact: after substituting `b = ⟨x,y⟩` the three cross terms
collapse to three copies of `⟨y,x⟩⟨x,y⟩`, and one factor of `‖⟨x,x⟩‖` is left
over to be cancelled --- which is legitimate precisely when `x ≠ 0`, and the
case `x = 0` is where definiteness of the inner product is used.

## Instances

`[PartialOrder B]` and `[StarOrderedRing B]` are hypotheses, not instances, as
in mathlib: a Hilbert module is *defined* without an order on `B` and *normed*
with one.  Files that need only the algebra of `𝓚(E)` --- `CStarFiniteRank` ---
do not carry them.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace CStarModule

variable (E : CStarModule.{v, w} B)

/-! ## The norm -/

/-- `⟨x,x⟩` is positive in the order, not merely of the form `z⋆z`. -/
theorem inner_self_nonneg (x : E.carrier) : 0 ≤ E.inner x x :=
  (E.inner_self_isPositive x).nonneg

/-- **The norm of a Hilbert C⋆-module**, `‖x‖ = ‖⟨x,x⟩‖^{1/2}`.

It is a plain function rather than a `Norm` instance: the carrier of a bundled
module is a field of a structure, so an instance would have to be found by
unification through a projection.  `toNormedAddCommGroup` packages it for the
places that want the instance. -/
noncomputable def norm (x : E.carrier) : ℝ := Real.sqrt ‖E.inner x x‖

omit [PartialOrder B] [StarOrderedRing B] in
theorem norm_def (x : E.carrier) : E.norm x = Real.sqrt ‖E.inner x x‖ := rfl

omit [PartialOrder B] [StarOrderedRing B] in
protected theorem norm_nonneg (x : E.carrier) : 0 ≤ E.norm x :=
  Real.sqrt_nonneg _

omit [PartialOrder B] [StarOrderedRing B] in
/-- The defining identity in its usable form: the *square* of the norm is the
norm of the inner product. -/
theorem norm_sq (x : E.carrier) : E.norm x ^ 2 = ‖E.inner x x‖ :=
  Real.sq_sqrt (_root_.norm_nonneg _)

omit [PartialOrder B] [StarOrderedRing B] in
theorem norm_eq_zero_iff (x : E.carrier) : E.norm x = 0 ↔ x = 0 := by
  rw [norm_def, Real.sqrt_eq_zero (_root_.norm_nonneg _), norm_eq_zero]
  exact ⟨fun h => E.inner_self_eq_zero x h, fun h => by
    rw [h, E.inner_zero_left]⟩

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem norm_zero_vector : E.norm (0 : E.carrier) = 0 :=
  (E.norm_eq_zero_iff 0).mpr rfl

/-! ## Cauchy--Schwarz -/

/-- The positivity of `⟨x·b - ‖⟨x,x⟩‖y, x·b - ‖⟨x,x⟩‖y⟩`, expanded and with
its leading term dominated by `‖⟨x,x⟩‖ • b⋆b`.

This is the whole analytic content; `inner_mul_inner_swap_le` is the
substitution `b = ⟨x,y⟩` and one cancellation. -/
theorem cauchySchwarzAux (x y : E.carrier) (b : B) :
    (0 : B) ≤ ‖E.inner x x‖ • (star b * b)
        - ‖E.inner x x‖ • (star b * E.inner x y)
        - ‖E.inner x x‖ • (E.inner y x * b)
        + ‖E.inner x x‖ • (‖E.inner x x‖ • E.inner y y) := by
  have hz : (0 : B) ≤ E.inner
      (E.act x b - (‖E.inner x x‖ : ℂ) • y)
      (E.act x b - (‖E.inner x x‖ : ℂ) • y) :=
    E.inner_self_nonneg _
  have hu : E.inner (E.act x b) (E.act x b) = star b * E.inner x x * b := by
    rw [E.inner_act_left, E.inner_act_right, ← mul_assoc]
  have huv : E.inner (E.act x b) ((‖E.inner x x‖ : ℂ) • y)
      = ‖E.inner x x‖ • (star b * E.inner x y) := by
    rw [E.inner_smul_right, E.inner_act_left, Complex.coe_smul]
  have hvu : E.inner ((‖E.inner x x‖ : ℂ) • y) (E.act x b)
      = ‖E.inner x x‖ • (E.inner y x * b) := by
    rw [E.inner_smul_left, Complex.conj_ofReal, E.inner_act_right,
      Complex.coe_smul]
  have hvv : E.inner ((‖E.inner x x‖ : ℂ) • y) ((‖E.inner x x‖ : ℂ) • y)
      = ‖E.inner x x‖ • (‖E.inner x x‖ • E.inner y y) := by
    rw [E.inner_smul_left, Complex.conj_ofReal, E.inner_smul_right]
    simp only [Complex.coe_smul]
  have hexp : E.inner
      (E.act x b - (‖E.inner x x‖ : ℂ) • y)
      (E.act x b - (‖E.inner x x‖ : ℂ) • y)
      = star b * E.inner x x * b
        - ‖E.inner x x‖ • (star b * E.inner x y)
        - ‖E.inner x x‖ • (E.inner y x * b)
        + ‖E.inner x x‖ • (‖E.inner x x‖ • E.inner y y) := by
    rw [E.inner_sub_left, E.inner_sub_right, E.inner_sub_right, hu, huv, hvu,
      hvv]
    abel
  rw [hexp] at hz
  refine le_trans hz ?_
  exact add_le_add_left (sub_le_sub_right (sub_le_sub_right
    (OrderZero.star_conjugate_le_norm_smul (E.inner_self_isSelfAdjoint x) b)
      _) _) _

/-- **The C⋆-valued Cauchy--Schwarz inequality.**

`⟨y,x⟩⟨x,y⟩ ≤ ‖⟨x,x⟩‖ • ⟨y,y⟩`.  Both sides are positive elements of `B`, and
the scalar on the right cannot be replaced by `⟨x,x⟩`: the naive
`⟨x,x⟩⟨y,y⟩` is not even selfadjoint. -/
theorem inner_mul_inner_swap_le (x y : E.carrier) :
    E.inner y x * E.inner x y ≤ ‖E.inner x x‖ • E.inner y y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [E.inner_zero_left, E.inner_zero_right]
  · have hxx : E.inner x x ≠ 0 := fun h => hx (E.inner_self_eq_zero x h)
    have hnpos : 0 < ‖E.inner x x‖ := norm_pos_iff.mpr hxx
    have h := E.cauchySchwarzAux x y (E.inner x y)
    rw [E.inner_star x y] at h
    have hcollapse :
        ‖E.inner x x‖ • (E.inner y x * E.inner x y)
            - ‖E.inner x x‖ • (E.inner y x * E.inner x y)
            - ‖E.inner x x‖ • (E.inner y x * E.inner x y)
            + ‖E.inner x x‖ • (‖E.inner x x‖ • E.inner y y)
          = ‖E.inner x x‖ • (‖E.inner x x‖ • E.inner y y
              - E.inner y x * E.inner x y) := by
      rw [smul_sub]
      abel
    rw [hcollapse] at h
    have h' : ‖E.inner x x‖ • (0 : B)
        ≤ ‖E.inner x x‖ • (‖E.inner x x‖ • E.inner y y
            - E.inner y x * E.inner x y) := by
      rw [smul_zero]
      exact h
    exact sub_nonneg.mp ((smul_le_smul_iff_of_pos_left hnpos).mp h')

/-- **The scalar Cauchy--Schwarz inequality**, `‖⟨x,y⟩‖ ≤ ‖x‖‖y‖`. -/
theorem norm_inner_le (x y : E.carrier) :
    ‖E.inner x y‖ ≤ E.norm x * E.norm y := by
  have hsq : ‖E.inner x y‖ ^ 2 ≤ (E.norm x * E.norm y) ^ 2 := by
    have h1 : ‖E.inner x y‖ ^ 2 = ‖E.inner y x * E.inner x y‖ := by
      rw [← E.inner_star x y, CStarRing.norm_star_mul_self, pow_two]
    have h2 : ‖E.inner y x * E.inner x y‖
        ≤ ‖‖E.inner x x‖ • E.inner y y‖ := by
      refine OrderZero.norm_le_norm_of_nonneg_of_le ?_
        (E.inner_mul_inner_swap_le x y)
      rw [← E.inner_star x y]
      exact star_mul_self_nonneg _
    have h3 : ‖‖E.inner x x‖ • E.inner y y‖ = (E.norm x * E.norm y) ^ 2 := by
      rw [norm_smul, mul_pow, E.norm_sq, E.norm_sq, Real.norm_eq_abs,
        abs_of_nonneg (_root_.norm_nonneg _)]
    rw [h1, ← h3]
    exact h2
  refine (pow_le_pow_iff_left₀ (_root_.norm_nonneg _) ?_
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact mul_nonneg (E.norm_nonneg x) (E.norm_nonneg y)

/-! ## The norm axioms -/

omit [PartialOrder B] [StarOrderedRing B] in
protected theorem norm_smul (c : ℂ) (x : E.carrier) :
    E.norm (c • x) = ‖c‖ * E.norm x := by
  have h : E.inner (c • x) (c • x)
      = ((starRingEnd ℂ) c * c) • E.inner x x := by
    rw [E.inner_smul_left, E.inner_smul_right, smul_smul]
  have hnorm : ‖E.inner (c • x) (c • x)‖ = ‖c‖ ^ 2 * ‖E.inner x x‖ := by
    rw [h, norm_smul, starRingEnd_apply, norm_mul, norm_star, ← pow_two]
  rw [norm_def, norm_def, hnorm, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (_root_.norm_nonneg c)]

omit [PartialOrder B] [StarOrderedRing B] in
theorem norm_neg (x : E.carrier) : E.norm (-x) = E.norm x := by
  have h : -x = (-1 : ℂ) • x := (neg_one_smul ℂ x).symm
  rw [h, E.norm_smul]
  simp

/-- **The action is contractive**: `‖x·b‖ ≤ ‖x‖‖b‖`.

This is the estimate that makes `θ_{x,y} : z ↦ x·⟨y,z⟩` a bounded operator,
and hence the estimate the operator norm on `𝓛(E)` rests on. -/
theorem norm_act_le (x : E.carrier) (b : B) :
    E.norm (E.act x b) ≤ E.norm x * ‖b‖ := by
  have hle : E.inner (E.act x b) (E.act x b)
      ≤ ‖E.inner x x‖ • (star b * b) := by
    have hu : E.inner (E.act x b) (E.act x b) = star b * E.inner x x * b := by
      rw [E.inner_act_left, E.inner_act_right, ← mul_assoc]
    rw [hu]
    exact OrderZero.star_conjugate_le_norm_smul (E.inner_self_isSelfAdjoint x) b
  have hnorm : ‖E.inner (E.act x b) (E.act x b)‖
      ≤ ‖E.inner x x‖ * ‖b‖ ^ 2 := by
    refine le_trans (OrderZero.norm_le_norm_of_nonneg_of_le
      (E.inner_self_nonneg _) hle) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (_root_.norm_nonneg _),
      CStarRing.norm_star_mul_self, ← pow_two]
  have hsq : E.norm (E.act x b) ^ 2 ≤ (E.norm x * ‖b‖) ^ 2 := by
    rw [E.norm_sq, mul_pow, E.norm_sq]
    exact hnorm
  refine (pow_le_pow_iff_left₀ (E.norm_nonneg _) ?_
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact mul_nonneg (E.norm_nonneg x) (_root_.norm_nonneg b)

protected theorem norm_add_le (x y : E.carrier) :
    E.norm (x + y) ≤ E.norm x + E.norm y := by
  have hexp : E.inner (x + y) (x + y)
      = E.inner x x + E.inner x y + E.inner y x + E.inner y y := by
    rw [E.inner_add_left, E.inner_add_right, E.inner_add_right]
    abel
  have hsq : E.norm (x + y) ^ 2 ≤ (E.norm x + E.norm y) ^ 2 := by
    have h1 : E.norm (x + y) ^ 2
        = ‖E.inner x x + E.inner x y + E.inner y x + E.inner y y‖ := by
      rw [E.norm_sq, hexp]
    have h2 : ‖E.inner x x + E.inner x y + E.inner y x + E.inner y y‖
        ≤ ‖E.inner x x‖ + ‖E.inner x y‖ + ‖E.inner y x‖ + ‖E.inner y y‖ := by
      calc
        ‖E.inner x x + E.inner x y + E.inner y x + E.inner y y‖
            ≤ ‖E.inner x x + E.inner x y + E.inner y x‖ + ‖E.inner y y‖ :=
              norm_add_le _ _
        _ ≤ (‖E.inner x x + E.inner x y‖ + ‖E.inner y x‖) + ‖E.inner y y‖ :=
              add_le_add_left (norm_add_le _ _) _
        _ ≤ (‖E.inner x x‖ + ‖E.inner x y‖ + ‖E.inner y x‖) +
              ‖E.inner y y‖ :=
              add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
    have h3 : ‖E.inner x x‖ + ‖E.inner x y‖ + ‖E.inner y x‖ + ‖E.inner y y‖
        ≤ E.norm x ^ 2 + E.norm x * E.norm y + E.norm y * E.norm x
          + E.norm y ^ 2 := by
      refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
      · exact le_of_eq (E.norm_sq x).symm
      · exact E.norm_inner_le x y
      · exact E.norm_inner_le y x
      · exact le_of_eq (E.norm_sq y).symm
    have h4 : E.norm x ^ 2 + E.norm x * E.norm y + E.norm y * E.norm x
        + E.norm y ^ 2 = (E.norm x + E.norm y) ^ 2 := by ring
    rw [h1, ← h4]
    exact le_trans h2 h3
  refine (pow_le_pow_iff_left₀ (E.norm_nonneg _) ?_
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact add_nonneg (E.norm_nonneg x) (E.norm_nonneg y)

/-- The triangle inequality over a finite sum, by induction.  It is what
bounds a finite-rank operator, hence what makes `𝓚(E)` a set of *bounded*
operators. -/
theorem norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → E.carrier) :
    E.norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, E.norm (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact le_trans (E.norm_add_le _ _) (add_le_add_right ih _)

/-! ## Packaging

The four facts above are exactly the axioms of a normed space, so the carrier
of any Hilbert module may be regarded as one.  This is a `def` and not an
instance --- the module is data, so the norm cannot be found by instance
search --- and it is used by naming it with `letI` at the point of use. -/

/-- The carrier of a Hilbert C⋆-module, as a normed additive group. -/
@[reducible] noncomputable def toNormedAddCommGroup : NormedAddCommGroup E.carrier :=
  letI : Norm E.carrier := ⟨E.norm⟩
  have core : NormedSpace.Core ℂ E.carrier :=
    { norm_nonneg := E.norm_nonneg
      norm_smul := E.norm_smul
      norm_triangle := E.norm_add_le
      norm_eq_zero_iff := E.norm_eq_zero_iff }
  NormedAddCommGroup.ofCore core

end CStarModule

/-! ## The self-module

Its norm is the C⋆-norm.  This is the compatibility statement that lets an
estimate proved for a general module be read as an estimate in `B`, and it is
the C⋆-identity again. -/

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem selfModule_norm (b : B) : (selfModule B).norm b = ‖b‖ := by
  rw [CStarModule.norm_def, selfModule_inner, CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg b)]

end HilbertModule
end GroupApproximation
