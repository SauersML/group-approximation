import GroupApproximation.Analysis.CStarOrderZero

/-!
# Positivity as an order, and the two conjugation estimates

`Analysis.CStarOrderZero` spells positivity as `IsPositiveElem a : ∃ z, a = z⋆z`
and never as `0 ≤ a`, because the concrete algebras of this development are
closed `StarSubalgebra`s of `B(H)` and carry no `PartialOrder`.  That spelling
is enough for every *algebraic* statement, and it has carried the order-zero
layer, the Hilbert-module layer and the finite-rank ideal.

It is not enough for Cauchy--Schwarz.  The `B`-valued Cauchy--Schwarz
inequality is an *inequality*, and its proof is an order argument: expand
`0 ≤ ⟨x·b - λy, x·b - λy⟩`, dominate the leading term by
`b⋆⟨x,x⟩b ≤ ‖⟨x,x⟩‖·b⋆b`, and cancel.  So the module norm --- hence the
compact operators, hence Fredholm theory, hence `KK` --- is separated from the
algebra already built by exactly this file: the dictionary between the two
spellings, and the two estimates the argument consumes.

## What is proved

Nothing here is new mathematics; all of it is a re-statement of mathlib in the
vocabulary the rest of this development uses, and that re-statement is the
point --- downstream files quote these names and never `StarOrderedRing`.

* `isPositiveElem_iff_nonneg` --- the dictionary, in both directions.
* `conjugate_le_conjugate` --- `a ≤ b → c⋆ac ≤ c⋆bc`.
* `star_conjugate_le_norm_smul` --- `c⋆ac ≤ ‖a‖ • c⋆c` for selfadjoint `a`.
  This is the *quantitative* half: it is where the scalar `‖⟨x,x⟩‖` that
  appears in Cauchy--Schwarz comes from, and it is why the inequality has a
  norm in it at all rather than being a purely algebraic comparison.
* `norm_le_norm_of_nonneg_of_le` --- monotonicity of the norm on positives,
  which turns the `B`-valued inequality into the scalar one.
* `star_add_mul_self_le` --- `(a+b)⋆(a+b) ≤ 2(a⋆a + b⋆b)`, the parallelogram
  estimate.  It is not used by Cauchy--Schwarz; it is what makes the set of
  square-summable sequences over `B` closed under addition, i.e. what makes
  the standard module `H_B` a module.

## The instance discipline

Every statement below carries `[PartialOrder B] [StarOrderedRing B]` as
hypotheses, exactly as mathlib does: a C⋆-algebra has a canonical order, but
mathlib does not register it as an instance, since a type may already carry an
unrelated order.  Downstream files inherit this discipline --- a Hilbert module
needs no order to be *defined*, and needs one to be *normed*.
-/

namespace GroupApproximation
namespace OrderZero

universe u

section Order

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## The dictionary -/

/-- **Positivity in the `z⋆z` spelling is positivity in the order.**

The forward direction is `star_mul_self_nonneg`; the reverse is the
continuous functional calculus, `a = √a · √a` with `√a` selfadjoint.  Both are
mathlib's `CStarAlgebra.nonneg_iff_eq_star_mul_self`, which is available for a
*non-unital* C⋆-algebra with an order, which is the generality this
development needs. -/
theorem isPositiveElem_iff_nonneg {a : A} : IsPositiveElem a ↔ 0 ≤ a :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.symm

theorem IsPositiveElem.nonneg {a : A} (ha : IsPositiveElem a) : 0 ≤ a :=
  isPositiveElem_iff_nonneg.mp ha

theorem isPositiveElem_of_nonneg {a : A} (ha : 0 ≤ a) : IsPositiveElem a :=
  isPositiveElem_iff_nonneg.mpr ha

/-- Positivity is closed under sums, in either spelling.  The `z⋆z` spelling
makes this *false-looking* --- a sum of two squares need not visibly be a
square --- and it is exactly the dictionary that repairs it. -/
theorem IsPositiveElem.add {a b : A} (ha : IsPositiveElem a)
    (hb : IsPositiveElem b) : IsPositiveElem (a + b) :=
  isPositiveElem_of_nonneg (add_nonneg ha.nonneg hb.nonneg)

/-! ## The two conjugation estimates -/

/-- **Conjugation is monotone**: `a ≤ b` gives `c⋆ac ≤ c⋆bc`. -/
theorem conjugate_le_conjugate {a b : A} (hab : a ≤ b) (c : A) :
    star c * a * c ≤ star c * b * c :=
  star_left_conjugate_le_conjugate hab c

/-- **The quantitative conjugation estimate**: for selfadjoint `a`,
`c⋆ac ≤ ‖a‖ • c⋆c`.

This is monotonicity applied to `a ≤ ‖a‖·1` in the unitization, pushed back
into `A`; mathlib does the pushing, and the statement is genuinely about `A`
even though its proof is not. -/
theorem star_conjugate_le_norm_smul {a : A} (ha : IsSelfAdjoint a) (c : A) :
    star c * a * c ≤ ‖a‖ • (star c * c) :=
  CStarAlgebra.star_left_conjugate_le_norm_smul ha

/-- The same estimate on the other side. -/
theorem conjugate_star_le_norm_smul {a : A} (ha : IsSelfAdjoint a) (c : A) :
    c * a * star c ≤ ‖a‖ • (c * star c) :=
  CStarAlgebra.star_right_conjugate_le_norm_smul ha

/-- **The norm is monotone on positive elements.**  This is the step that
turns a `B`-valued inequality into a scalar one, and it is the only place the
scalar Cauchy--Schwarz inequality uses about the order. -/
theorem norm_le_norm_of_nonneg_of_le {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

/-! ## The parallelogram estimate

Not used below; used by the standard module `H_B`, whose vectors are the
sequences with `∑ bᵢ⋆bᵢ` convergent.  Closure of that condition under addition
is precisely this inequality. -/

/-- **Cross terms are dominated by the diagonal**: `a⋆b + b⋆a ≤ a⋆a + b⋆b`.

Expand `0 ≤ (a-b)⋆(a-b)`. -/
theorem star_mul_add_star_mul_le {a b : A} :
    star a * b + star b * a ≤ star a * a + star b * b := by
  have h : (0 : A) ≤ star (a - b) * (a - b) := star_mul_self_nonneg _
  have hexp : star (a - b) * (a - b)
      = (star a * a + star b * b) - (star a * b + star b * a) := by
    rw [star_sub, sub_mul, mul_sub, mul_sub]
    abel
  rw [hexp, sub_nonneg] at h
  exact h

/-- **The parallelogram estimate**: `(a+b)⋆(a+b) ≤ 2(a⋆a + b⋆b)`, stated
without a scalar action as a sum of two copies. -/
theorem star_add_mul_self_le {a b : A} :
    star (a + b) * (a + b)
      ≤ (star a * a + star b * b) + (star a * a + star b * b) := by
  have hexp : star (a + b) * (a + b)
      = (star a * a + star b * b) + (star a * b + star b * a) := by
    rw [star_add, add_mul, mul_add, mul_add]
    abel
  rw [hexp]
  exact add_le_add_right (star_mul_add_star_mul_le (a := a) (b := b)) _

end Order

end OrderZero
end GroupApproximation
