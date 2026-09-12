import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Unital corners of C-star algebras

For a self-adjoint idempotent `e` in a unital C-star algebra `A`, the
two-sided corner `eAe` is a unital C-star algebra whose unit is `e`.  Mathlib
already supplies the nonunital C-star structure on a closed nonunital star
subalgebra; this file supplies the changed unit and the resulting unital
structure.

This is the corner used by the two-by-two full-amalgam model of the universal
C-star HNN algebra.
-/

namespace GroupApproximation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The nonunital closed star subalgebra consisting of elements supported on
both sides by a self-adjoint idempotent `e`. -/
def cStarCornerSubalgebra (e : A) (he_star : star e = e) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {x | e * x = x ∧ x * e = x}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    constructor
    · simpa only [mul_add] using congrArg₂ (.+.) hx₁ hy₁
    · simpa only [add_mul] using congrArg₂ (.+.) hx₂ hy₂
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    constructor
    · rw [← mul_assoc, hx₁]
    · rw [mul_assoc, hy₂]
  smul_mem' := by
    rintro r x ⟨hx₁, hx₂⟩
    constructor
    · simpa only [mul_smul_comm] using congrArg (r • ·) hx₁
    · simpa only [smul_mul_assoc] using congrArg (r • ·) hx₂
  star_mem' := by
    rintro x ⟨hx₁, hx₂⟩
    constructor
    · calc
        e * star x = star e * star x := by rw [he_star]
        _ = star (x * e) := by rw [star_mul]
        _ = star x := congrArg star hx₂
    · calc
        star x * e = star x * star e := by rw [he_star]
        _ = star (e * x) := by rw [star_mul]
        _ = star x := congrArg star hx₁

/-- The carrier of a C-star corner is closed. -/
instance cStarCornerSubalgebra_isClosed (e : A) (he_star : star e = e) :
    IsClosed (cStarCornerSubalgebra e he_star : Set A) := by
  change IsClosed {x : A | e * x = x ∧ x * e = x}
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

/-- The unital corner supported by `e`. -/
abbrev CStarCorner (e : A) (he_star : star e = e) (_he_mul : e * e = e) : Type u :=
  cStarCornerSubalgebra e he_star

namespace CStarCorner

variable (e : A) (he_star : star e = e) (he_mul : e * e = e)

instance : One (CStarCorner e he_star he_mul) :=
  ⟨⟨e, he_mul, he_mul⟩⟩

@[simp] theorem coe_one :
    ((1 : CStarCorner e he_star he_mul) : A) = e :=
  rfl

instance : Monoid (CStarCorner e he_star he_mul) where
  one := 1
  mul := (· * ·)
  one_mul x := Subtype.ext x.property.1
  mul_one x := Subtype.ext x.property.2
  mul_assoc := mul_assoc
  npow := npowRec
  npow_zero _ := rfl
  npow_succ _ _ := rfl

instance : NatCast (CStarCorner e he_star he_mul) :=
  ⟨Nat.unaryCast⟩

instance : Semiring (CStarCorner e he_star he_mul) :=
  Semiring.mk
    (fun x ↦ Subtype.ext (zero_mul (x : A)))
    (fun x ↦ Subtype.ext (mul_zero (x : A)))
    (fun x y z ↦ Subtype.ext (mul_add (x : A) y z))
    (fun x y z ↦ Subtype.ext (add_mul (x : A) y z))
    (natCast_zero := by rfl)
    (natCast_succ := by intro n; rfl)

instance : IntCast (CStarCorner e he_star he_mul) :=
  ⟨Int.castDef⟩

instance : Ring (CStarCorner e he_star he_mul) :=
  Ring.mk
    (sub_eq_add_neg := by
      intro x y
      exact SubNegMonoid.sub_eq_add_neg x y)
    (zsmul_zero' := by
      intro x
      exact SubNegMonoid.zsmul_zero' x)
    (zsmul_succ' := by
      intro n x
      exact SubNegMonoid.zsmul_succ' n x)
    (zsmul_neg' := by
      intro n x
      exact SubNegMonoid.zsmul_neg' n x)
    (neg_add_cancel := fun x ↦ neg_add_cancel x)
    (intCast_ofNat := by intro n; rfl)
    (intCast_negSucc := by intro n; rfl)

instance : NormedRing (CStarCorner e he_star he_mul) where
  toRing := inferInstance
  toMetricSpace := inferInstance
  dist_eq x y := by
    change dist (x : A) (y : A) = ‖-(x : A) + (y : A)‖
    exact dist_eq_norm_neg_add (x : A) (y : A)
  norm_mul_le x y := NonUnitalNormedRing.norm_mul_le (x : A) (y : A)

instance : Algebra ℂ (CStarCorner e he_star he_mul) :=
  Algebra.ofModule
    (fun r x y ↦ Subtype.ext (smul_mul_assoc r (x : A) (y : A)))
    (fun r x y ↦ Subtype.ext (mul_smul_comm r (x : A) (y : A)))

instance : NormedAlgebra ℂ (CStarCorner e he_star he_mul) where
  norm_smul_le := norm_smul_le

noncomputable instance : CStarAlgebra (CStarCorner e he_star he_mul) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The canonical nonunital inclusion of a corner into its ambient algebra. -/
def inclusion : CStarCorner e he_star he_mul →⋆ₙₐ[ℂ] A :=
  NonUnitalStarSubalgebraClass.subtype (cStarCornerSubalgebra e he_star)

@[simp] theorem inclusion_apply (x : CStarCorner e he_star he_mul) :
    inclusion e he_star he_mul x = (x : A) :=
  rfl

end CStarCorner

end

end GroupApproximation
