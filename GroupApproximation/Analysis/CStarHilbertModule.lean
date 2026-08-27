import GroupApproximation.Analysis.CStarOrderZero

/-!
# Hilbert C⋆-modules

`Analysis.KKTheoryKasparov` records that `KK(A,B)` cannot be constructed in
this development because "there are no Hilbert C⋆-modules, no multiplier
algebras, no Fredholm theory over a C⋆-algebra".  This file removes the first
of those three.

A Hilbert C⋆-module over `B` is a right `B`-module `E` carrying a `B`-valued
inner product: conjugate-symmetric, `B`-linear in the second variable, positive
and definite.  Kasparov modules are pairs of such things, so this is the
category the whole theory lives in.

## What is proved

Everything, unconditionally.  The axioms are stated for the second variable
only, and the first-variable versions --- additivity, conjugate linearity, and
`⟨x·b, y⟩ = b⋆⟨x,y⟩` --- are **derived** from conjugate symmetry rather than
assumed, which is what keeps the structure as weak as the mathematics:

* `inner_add_left`, `inner_sub_left`, `inner_zero_left`, `inner_smul_left`,
  `inner_act_left`;
* `eq_zero_of_inner_eq_zero` --- an element orthogonal to everything is `0`,
  which is definiteness read as a separation property and is the engine of
  every uniqueness argument about adjointable operators;
* `selfModule` --- **`B` is a Hilbert module over itself** with
  `⟨x,y⟩ = x⋆y`, the module on which the multiplier algebra lives.  Its
  definiteness clause is the C⋆-identity: `‖x⋆x‖ = ‖x‖²`.

## Spelling

Positivity of `⟨x,x⟩` is `OrderZero.IsPositiveElem` --- `∃ z, ⟨x,x⟩ = z⋆z` ---
and not `0 ≤ ⟨x,x⟩`, matching `CStarExactness.IsCompletelyPositive` and the
order-zero layer, so that no `PartialOrder`/`StarOrderedRing` instance is
required of `B`.  The two agree on a C⋆-algebra.

The module is **bundled** rather than presented as a class over a carrier with
`SMul`/`Module` instances.  A class would need a right action of `B` on `E`,
hence `SMul Bᵐᵒᵖ E` and a compatibility diamond with the `ℂ`-action; bundling
sidesteps that entirely, and every construction in `KK`-theory produces the
module as data anyway.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w

/-- **A right Hilbert C⋆-module over `B`**, bundled with its operations.

The inner product takes values in `B`, is additive and `ℂ`-linear in its
second variable, satisfies `⟨x, y·b⟩ = ⟨x,y⟩·b`, is conjugate-symmetric, and is
positive and definite. -/
structure CStarModule (B : Type v) [NonUnitalCStarAlgebra B] where
  /-- The underlying set of vectors. -/
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The right action of `B`. -/
  act : carrier → B → carrier
  /-- The `B`-valued inner product. -/
  inner : carrier → carrier → B
  /-- The action is additive in the vector. -/
  act_add_left : ∀ (x y : carrier) (b : B), act (x + y) b = act x b + act y b
  /-- The action is additive in the scalar. -/
  act_add_right : ∀ (x : carrier) (b c : B), act x (b + c) = act x b + act x c
  /-- The action is associative. -/
  act_assoc : ∀ (x : carrier) (b c : B), act (act x b) c = act x (b * c)
  /-- The two actions commute. -/
  act_smul : ∀ (c : ℂ) (x : carrier) (b : B), act (c • x) b = c • act x b
  /-- The inner product is additive in the second variable. -/
  inner_add_right : ∀ x y z : carrier,
    inner x (y + z) = inner x y + inner x z
  /-- The inner product is `ℂ`-linear in the second variable. -/
  inner_smul_right : ∀ (c : ℂ) (x y : carrier),
    inner x (c • y) = c • inner x y
  /-- The inner product is `B`-linear in the second variable. -/
  inner_act_right : ∀ (x y : carrier) (b : B),
    inner x (act y b) = inner x y * b
  /-- The inner product is conjugate-symmetric. -/
  inner_star : ∀ x y : carrier, star (inner x y) = inner y x
  /-- The inner product is positive. -/
  inner_self_isPositive : ∀ x : carrier, IsPositiveElem (inner x x)
  /-- The inner product is definite. -/
  inner_self_eq_zero : ∀ x : carrier, inner x x = 0 → x = 0

attribute [instance] CStarModule.addCommGroup CStarModule.module

namespace CStarModule

variable {B : Type v} [NonUnitalCStarAlgebra B] (E : CStarModule.{v, w} B)

/-! ## The first variable

Nothing below is an axiom: each is the corresponding second-variable axiom
read through conjugate symmetry. -/

theorem inner_add_left (x y z : E.carrier) :
    E.inner (x + y) z = E.inner x z + E.inner y z := by
  have h : star (E.inner (x + y) z) = star (E.inner x z + E.inner y z) := by
    rw [E.inner_star, star_add, E.inner_star, E.inner_star, E.inner_add_right]
  have h2 := congrArg star h
  rwa [star_star, star_star] at h2

theorem inner_zero_right (x : E.carrier) : E.inner x 0 = 0 := by
  have h : E.inner x 0 = E.inner x 0 + E.inner x 0 := by
    rw [← E.inner_add_right, add_zero]
  exact left_eq_add.mp h

theorem inner_zero_left (x : E.carrier) : E.inner 0 x = 0 := by
  have h := E.inner_star x 0
  rw [E.inner_zero_right, star_zero] at h
  exact h.symm

theorem inner_sub_right (x y z : E.carrier) :
    E.inner x (y - z) = E.inner x y - E.inner x z := by
  have h : E.inner x (y - z) + E.inner x z = E.inner x y := by
    rw [← E.inner_add_right]
    congr 1
    abel
  exact eq_sub_of_add_eq h

theorem inner_sub_left (x y z : E.carrier) :
    E.inner (x - y) z = E.inner x z - E.inner y z := by
  have h : E.inner (x - y) z + E.inner y z = E.inner x z := by
    rw [← E.inner_add_left]
    congr 1
    abel
  exact eq_sub_of_add_eq h

theorem inner_act_left (x y : E.carrier) (b : B) :
    E.inner (E.act x b) y = star b * E.inner x y := by
  have h : star (E.inner (E.act x b) y) = star (star b * E.inner x y) := by
    rw [E.inner_star, star_mul, star_star, E.inner_star, E.inner_act_right]
  have h2 := congrArg star h
  rwa [star_star, star_star] at h2

/-- The inner product is conjugate-linear in the first variable. -/
theorem inner_smul_left (c : ℂ) (x y : E.carrier) :
    E.inner (c • x) y = (starRingEnd ℂ) c • E.inner x y := by
  have h : star (E.inner (c • x) y)
      = star ((starRingEnd ℂ) c • E.inner x y) := by
    rw [E.inner_star, E.inner_smul_right, star_smul, starRingEnd_apply,
      star_star, E.inner_star]
  have h2 := congrArg star h
  rwa [star_star, star_star] at h2

theorem inner_self_isSelfAdjoint (x : E.carrier) :
    IsSelfAdjoint (E.inner x x) :=
  (E.inner_self_isPositive x).isSelfAdjoint

/-! ## Separation

Definiteness of the inner product, read as the statement that the inner
product separates points.  Every uniqueness statement about adjointable
operators is this lemma. -/

/-- **A vector orthogonal to every vector is zero.** -/
theorem eq_zero_of_inner_eq_zero {x : E.carrier}
    (h : ∀ y : E.carrier, E.inner y x = 0) : x = 0 :=
  E.inner_self_eq_zero x (h x)

/-- The separation property in the form the adjointable-operator lemmas use:
two vectors with the same inner products against everything are equal. -/
theorem eq_of_inner_eq {x z : E.carrier}
    (h : ∀ y : E.carrier, E.inner y x = E.inner y z) : x = z := by
  have hz : x - z = 0 := by
    refine E.eq_zero_of_inner_eq_zero fun y => ?_
    rw [E.inner_sub_right, h y, sub_self]
  exact sub_eq_zero.mp hz

end CStarModule

/-! ## `B` as a module over itself -/

/-- **A C⋆-algebra is a Hilbert module over itself**, with `⟨x,y⟩ = x⋆y`.

Definiteness is the C⋆-identity, and it is the only clause here that is not
pure algebra: `⟨x,x⟩ = 0` reads `‖x‖² = ‖x⋆x‖ = 0`.

This is the module whose adjointable operators are the multiplier algebra
`M(B)`, which is where the supporting `⋆`-homomorphism of a Winter--Zacharias
factorization lives, and where the Kasparov modules of `KK(A,B)` are
built. -/
@[reducible] def selfModule (B : Type v) [NonUnitalCStarAlgebra B] :
    CStarModule.{v, v} B where
  carrier := B
  act x b := x * b
  inner x y := star x * y
  act_add_left x y b := by rw [add_mul]
  act_add_right x b c := by rw [mul_add]
  act_assoc x b c := by rw [mul_assoc]
  act_smul c x b := by rw [smul_mul_assoc]
  inner_add_right x y z := by rw [mul_add]
  inner_smul_right c x y := by rw [mul_smul_comm]
  inner_act_right x y b := by rw [mul_assoc]
  inner_star x y := by rw [star_mul, star_star]
  inner_self_isPositive x := isPositiveElem_star_mul_self x
  inner_self_eq_zero x hx := by
    have h := CStarRing.norm_star_mul_self (x := x)
    rw [hx, norm_zero] at h
    have hx0 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hx0

@[simp] theorem selfModule_inner {B : Type v} [NonUnitalCStarAlgebra B]
    (x y : B) : (selfModule B).inner x y = star x * y := rfl

@[simp] theorem selfModule_act {B : Type v} [NonUnitalCStarAlgebra B]
    (x b : B) : (selfModule B).act x b = x * b := rfl

end HilbertModule
end GroupApproximation
