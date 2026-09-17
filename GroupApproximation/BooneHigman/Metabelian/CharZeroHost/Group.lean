import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Mul
import GroupApproximation.Meta.AxiomGuard

/-!
# The affine group `R^n ⋊ GL_n(R)` (lane bh-met-09)

Research claim (char-zero parameter-coordinate host): for `R = A[t_1, …, t_k]` the affine group
`R^n ⋊ Γ` acts self-similarly and faithfully on the tree over `X = F_p^n × F_p^k`.  This module
only builds the group: `vecAction n R : GL_n(R) →* MulAut (Multiplicative (R^n))` is matrix
multiplication, `Aff n R` is the semidirect product, and `vec`/`mat`/`mk` are the translation and
linear coordinates, with the product rule `vec (x * y) = vec x + mat x *ᵥ vec y` (by `rfl`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open scoped Matrix

variable (n : ℕ) (R : Type*) [CommRing R]

/-- `GL_n(R)` acting on the column vectors `Multiplicative (Fin n → R)` by matrix
multiplication. -/
def vecAction : GL (Fin n) R →* MulAut (Multiplicative (Fin n → R)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) R) *ᵥ v.toAdd)
      invFun := fun v =>
        Multiplicative.ofAdd ((↑g⁻¹ : Matrix (Fin n) (Fin n) R) *ᵥ v.toAdd)
      left_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
          ofAdd_toAdd]
      right_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec,
          ofAdd_toAdd]
      map_mul' := fun v w =>
        (congrArg Multiplicative.ofAdd
          (Matrix.mulVec_add (g : Matrix (Fin n) (Fin n) R) v.toAdd w.toAdd) :) }
  map_one' := MulEquiv.ext fun v =>
    (congrArg Multiplicative.ofAdd (Matrix.one_mulVec (Multiplicative.toAdd v)) :)
  map_mul' g h := MulEquiv.ext fun v =>
    (congrArg Multiplicative.ofAdd
      (Matrix.mulVec_mulVec (Multiplicative.toAdd v) (g : Matrix (Fin n) (Fin n) R)
        (h : Matrix (Fin n) (Fin n) R)).symm :)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.vecAction

/-- The affine group `R^n ⋊ GL_n(R)`. -/
abbrev Aff : Type _ := Multiplicative (Fin n → R) ⋊[vecAction n R] GL (Fin n) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Aff

variable {n R}

/-- The translation part of an affine map. -/
def vec (x : Aff n R) : Fin n → R := Multiplicative.toAdd x.left

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.vec

/-- The linear part of an affine map, as a matrix. -/
def mat (x : Aff n R) : Matrix (Fin n) (Fin n) R := (x.right : Matrix (Fin n) (Fin n) R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mat

/-- The affine map `v ↦ g v + w`. -/
def mk (w : Fin n → R) (g : GL (Fin n) R) : Aff n R := ⟨Multiplicative.ofAdd w, g⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mk

theorem vec_mul (x y : Aff n R) : vec (x * y) = vec x + mat x *ᵥ vec y := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.vec_mul

theorem mat_mul (x y : Aff n R) : mat (x * y) = mat x * mat y := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mat_mul

theorem vec_mk (w : Fin n → R) (g : GL (Fin n) R) : vec (mk w g) = w := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.vec_mk

theorem right_mk (w : Fin n → R) (g : GL (Fin n) R) : (mk w g).right = g := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.right_mk

theorem mat_mk (w : Fin n → R) (g : GL (Fin n) R) :
    mat (mk w g) = (g : Matrix (Fin n) (Fin n) R) := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mat_mk

theorem vec_one : vec (1 : Aff n R) = 0 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.vec_one

theorem mat_one : mat (1 : Aff n R) = 1 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mat_one

/-- An affine map with zero translation and identity linear part is the identity. -/
theorem eq_one_of_vec_mat {x : Aff n R} (hv : vec x = 0) (hm : mat x = 1) : x = 1 := by
  have hl : x.left = 1 := by
    show Multiplicative.ofAdd (vec x) = Multiplicative.ofAdd 0
    rw [hv]
  have hr : x.right = 1 := Units.ext hm
  exact SemidirectProduct.ext hl hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.eq_one_of_vec_mat

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
