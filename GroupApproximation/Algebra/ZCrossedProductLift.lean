import GroupApproximation.Pestov91.CrossedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting ℤ-crossed products along covariant pairs

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1723–1726:

> The unit $v=\sum_h u^h1_{C_h}$ implements $S_C$, and
> $P_C=\operatorname{LC}(C,k)\rtimes_{S_C}\mathbb Z$: split any
> partial shift with endpoints in $C$ according to its successive
> returns.

The map `LC(C, k) ⋊_{S_C} ℤ → P_C` of the printed step is determined by a coefficient map and a
unit that implements the action.  This module supplies that universal property for the algebraic
crossed products `A ⋊ ℤ = SkewMonoidAlgebra A (Multiplicative ℤ)` of `Pestov91.CrossedProduct`:

* `unitPowHom w`: the monoid homomorphism `ofAdd n ↦ w ^ n` of a unit `w`;
* `covariant_zpow`: if `w * φ a = φ (ofAdd 1 • a) * w` for all `a`, then
  `φ (ofAdd n • a) * w ^ n = w ^ n * φ a` for every integer `n`;
* `liftOfUnit φ w hw : A ⋊ ℤ →+* B`, with `liftOfUnit_single`, `liftOfUnit_C`,
  `liftOfUnit_unit_zpow`, `liftOfUnit_unit` and `liftOfUnit_sum_C_mul_unit_zpow`;
* `ringHom_ext`: a ring homomorphism out of `A ⋊ ℤ` is determined by its values on coefficients
  and on the implementing unit.

It is built on `SkewMonoidAlgebra.liftNCRingHom` at the Mathlib pin.
-/

namespace GroupApproximation
namespace Pestov91
namespace CrossedProduct

open SkewMonoidAlgebra (single)
open Multiplicative (ofAdd toAdd)

variable {A : Type*} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] {B : Type*} [Ring B]

/-- The monoid homomorphism `ofAdd n ↦ w ^ n` of a unit `w`. -/
noncomputable def unitPowHom (w : Bˣ) : Multiplicative ℤ →* B where
  toFun n := ((w ^ toAdd n : Bˣ) : B)
  map_one' := by
    show ((w ^ toAdd (1 : Multiplicative ℤ) : Bˣ) : B) = 1
    rw [toAdd_one, zpow_zero, Units.val_one]
  map_mul' m n := by
    show ((w ^ toAdd (m * n) : Bˣ) : B) = ((w ^ toAdd m : Bˣ) : B) * ((w ^ toAdd n : Bˣ) : B)
    rw [toAdd_mul, zpow_add, Units.val_mul]

theorem unitPowHom_apply (w : Bˣ) (n : Multiplicative ℤ) :
    unitPowHom w n = ((w ^ toAdd n : Bˣ) : B) :=
  rfl

/-- **Covariance in every power.**  If `w` implements the generator of the action on the image of
`φ`, then `w ^ n` implements `ofAdd n`. -/
theorem covariant_zpow (φ : A →+* B) (w : Bˣ)
    (hw : ∀ a, (w : B) * φ a = φ (ofAdd (1 : ℤ) • a) * w) (n : ℤ) (a : A) :
    φ (ofAdd n • a) * ((w ^ n : Bˣ) : B) = ((w ^ n : Bˣ) : B) * φ a := by
  have hw' : ∀ b, φ (ofAdd (-1 : ℤ) • b) * ((w⁻¹ : Bˣ) : B) = ((w⁻¹ : Bˣ) : B) * φ b := by
    intro b
    have h := hw (ofAdd (-1 : ℤ) • b)
    rw [← mul_smul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, one_smul] at h
    calc φ (ofAdd (-1 : ℤ) • b) * ((w⁻¹ : Bˣ) : B)
        = ((w⁻¹ : Bˣ) : B) * ((w : B) * φ (ofAdd (-1 : ℤ) • b)) * ((w⁻¹ : Bˣ) : B) := by
          rw [Units.inv_mul_cancel_left]
      _ = ((w⁻¹ : Bˣ) : B) * φ b := by
          rw [h, mul_assoc, Units.mul_inv_cancel_right]
  induction n using Int.induction_on generalizing a with
  | zero => rw [ofAdd_zero, one_smul, zpow_zero, Units.val_one, mul_one, one_mul]
  | succ i ih =>
    have h1 := ih (ofAdd (1 : ℤ) • a)
    calc φ (ofAdd ((i : ℤ) + 1) • a) * ((w ^ ((i : ℤ) + 1) : Bˣ) : B)
        = (φ (ofAdd (i : ℤ) • ofAdd (1 : ℤ) • a) * ((w ^ (i : ℤ) : Bˣ) : B)) * (w : B) := by
          rw [ofAdd_add, mul_smul, zpow_add_one, Units.val_mul, mul_assoc]
      _ = ((w ^ (i : ℤ) : Bˣ) : B) * (φ (ofAdd (1 : ℤ) • a) * (w : B)) := by
          rw [h1, mul_assoc]
      _ = ((w ^ ((i : ℤ) + 1) : Bˣ) : B) * φ a := by
          rw [← hw, zpow_add_one, Units.val_mul, mul_assoc]
  | pred i ih =>
    have h1 := ih (ofAdd (-1 : ℤ) • a)
    calc φ (ofAdd (-(i : ℤ) - 1) • a) * ((w ^ (-(i : ℤ) - 1) : Bˣ) : B)
        = (φ (ofAdd (-(i : ℤ)) • ofAdd (-1 : ℤ) • a) * ((w ^ (-(i : ℤ)) : Bˣ) : B)) *
            ((w⁻¹ : Bˣ) : B) := by
          rw [sub_eq_add_neg, ofAdd_add, mul_smul, zpow_add, zpow_neg_one, Units.val_mul, mul_assoc]
      _ = ((w ^ (-(i : ℤ)) : Bˣ) : B) * (φ (ofAdd (-1 : ℤ) • a) * ((w⁻¹ : Bˣ) : B)) := by
          rw [h1, mul_assoc]
      _ = ((w ^ (-(i : ℤ) - 1) : Bˣ) : B) * φ a := by
          rw [hw', sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, mul_assoc]

/-- **The lift along a covariant pair.**  A ring homomorphism `φ : A →+* B` and a unit `w` of `B`
with `w * φ a = φ (ofAdd 1 • a) * w` give the ring homomorphism `A ⋊ ℤ →+* B` sending `C a` to
`φ a` and `u` to `w`. -/
noncomputable def liftOfUnit (φ : A →+* B) (w : Bˣ)
    (hw : ∀ a, (w : B) * φ a = φ (ofAdd (1 : ℤ) • a) * w) :
    SkewMonoidAlgebra A (Multiplicative ℤ) →+* B :=
  SkewMonoidAlgebra.liftNCRingHom φ (unitPowHom w) fun {x y} => by
    show φ (y • x) * ((w ^ toAdd y : Bˣ) : B) = ((w ^ toAdd y : Bˣ) : B) * φ x
    have h := covariant_zpow φ w hw (toAdd y) x
    rwa [ofAdd_toAdd] at h

variable (φ : A →+* B) (w : Bˣ) (hw : ∀ a, (w : B) * φ a = φ (ofAdd (1 : ℤ) • a) * w)

theorem liftOfUnit_single (g : Multiplicative ℤ) (a : A) :
    liftOfUnit φ w hw (single g a) = φ a * ((w ^ toAdd g : Bˣ) : B) :=
  SkewMonoidAlgebra.liftNC_single (φ : A →+ B) (unitPowHom w) g a

/-- The lift sends `C a` to `φ a`. -/
theorem liftOfUnit_C (a : A) : liftOfUnit φ w hw (C a) = φ a := by
  rw [C_apply, liftOfUnit_single, toAdd_one, zpow_zero, Units.val_one, mul_one]

/-- The lift sends `u ^ n` to `w ^ n`. -/
theorem liftOfUnit_unit_zpow (n : ℤ) :
    liftOfUnit φ w hw ((unit ^ n : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) = ((w ^ n : Bˣ) : B) := by
  rw [val_unit_zpow, liftOfUnit_single, map_one, one_mul, toAdd_ofAdd]

/-- The lift sends `u` to `w`. -/
theorem liftOfUnit_unit :
    liftOfUnit φ w hw (unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) = (w : B) := by
  simpa only [zpow_one] using liftOfUnit_unit_zpow φ w hw 1

/-- The lift of a Laurent sum `∑_j C (c j) u^j` is `∑_j φ (c j) w^j`. -/
theorem liftOfUnit_sum_C_mul_unit_zpow (S : Finset ℤ) (c : ℤ → A) :
    liftOfUnit φ w hw (∑ j ∈ S, C (c j) *
        ((unit ^ j : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
          SkewMonoidAlgebra A (Multiplicative ℤ))) =
      ∑ j ∈ S, φ (c j) * ((w ^ j : Bˣ) : B) := by
  simp only [map_sum, map_mul, liftOfUnit_C, liftOfUnit_unit_zpow]

/-- **Uniqueness.**  Two ring homomorphisms out of `A ⋊ ℤ` that agree on coefficients and on the
implementing unit are equal. -/
theorem ringHom_ext {f g : SkewMonoidAlgebra A (Multiplicative ℤ) →+* B}
    (hC : ∀ a, f (C a) = g (C a))
    (hu : f (unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) =
      g (unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ)) :
    f = g := by
  have hU : Units.map (f : SkewMonoidAlgebra A (Multiplicative ℤ) →* B) unit =
      Units.map (g : SkewMonoidAlgebra A (Multiplicative ℤ) →* B) unit :=
    Units.ext hu
  have hpow : ∀ n : ℤ,
      f ((unit ^ n : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
        SkewMonoidAlgebra A (Multiplicative ℤ)) =
      g ((unit ^ n : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
        SkewMonoidAlgebra A (Multiplicative ℤ)) := fun n => by
    have h := congrArg (fun U : Bˣ => ((U ^ n : Bˣ) : B)) hU
    simpa only [← map_zpow, Units.coe_map, MonoidHom.coe_coe] using h
  refine RingHom.ext fun x => ?_
  obtain ⟨S, c, rfl⟩ := exists_sum_C_mul_unit_zpow x
  simp only [map_sum, map_mul, hC, hpow]

end CrossedProduct
end Pestov91
end GroupApproximation

#audit_axioms GroupApproximation.Pestov91.CrossedProduct.covariant_zpow
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.liftOfUnit_C
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.liftOfUnit_unit_zpow
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.ringHom_ext
