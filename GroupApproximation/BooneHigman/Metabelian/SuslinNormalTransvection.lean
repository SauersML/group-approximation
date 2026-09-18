import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin normality, part 1: rank-one transvections with orthogonal factors

Lane `bh-met-39b`.  Over a commutative ring `A`, write `InE(M)` when the matrix `M` is the
underlying matrix of an element of `E_ι(A)` (`SuslinNormalInE`).  This file shows that
`1 + x yᵀ ∈ E_ι(A)` whenever the vectors `x, y` have **pointwise orthogonal supports**,
i.e. `x m * y m = 0` for every index `m` (`suslinNormal_inE_of_pointwise`).  The proof splits
`x` and then `y` into coordinate vectors; a product `(1 + X)(1 + Y) = 1 + (X + Y)` whenever
`X * Y = 0`, and `e_k c ⊗ e_l d = c d E_{kl}` is elementary (or zero when `k = l`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- `M` is the underlying matrix of an element of the elementary group `E_ι(A)`. -/
def SuslinNormalInE (ι A : Type*) [Fintype ι] [DecidableEq ι] [CommRing A]
    (M : Matrix ι ι A) : Prop :=
  ∃ u ∈ elementaryGroup ι A, (u : Matrix ι ι A) = M

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinNormalInE

section Transvection

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

theorem suslinNormal_inE_one : SuslinNormalInE ι A 1 :=
  ⟨1, (elementaryGroup ι A).one_mem, Units.val_one⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_one

theorem suslinNormal_inE_mul {M N : Matrix ι ι A} (hM : SuslinNormalInE ι A M)
    (hN : SuslinNormalInE ι A N) : SuslinNormalInE ι A (M * N) := by
  obtain ⟨u, hu, rfl⟩ := hM
  obtain ⟨v, hv, rfl⟩ := hN
  exact ⟨u * v, (elementaryGroup ι A).mul_mem hu hv, Units.val_mul u v⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_mul

/-- If `X² = 0` and `1 + X` is elementary, then so is its inverse `1 - X`. -/
theorem suslinNormal_inE_sub_of_sq {X : Matrix ι ι A} (hXX : X * X = 0)
    (h : SuslinNormalInE ι A (1 + X)) : SuslinNormalInE ι A (1 - X) := by
  obtain ⟨u, hu, hval⟩ := h
  refine ⟨u⁻¹, (elementaryGroup ι A).inv_mem hu, ?_⟩
  have hprod : (u : Matrix ι ι A) * (1 - X) = 1 := by
    rw [hval]
    noncomm_ring [hXX]
  calc ((u⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A)
      = ((u⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) * ((u : Matrix ι ι A) * (1 - X)) := by
        rw [hprod, mul_one]
    _ = 1 - X := by rw [← mul_assoc, Units.inv_mul, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_sub_of_sq

/-- `(1 + X)(1 + Y) = 1 + (X + Y)` when `X * Y = 0`. -/
theorem suslinNormal_inE_add {X Y : Matrix ι ι A} (hX : SuslinNormalInE ι A (1 + X))
    (hY : SuslinNormalInE ι A (1 + Y)) (hXY : X * Y = 0) :
    SuslinNormalInE ι A (1 + (X + Y)) := by
  have hprod : (1 + X) * (1 + Y) = 1 + (X + Y) := by
    rw [mul_add, mul_one, add_mul, one_mul, hXY, add_zero, add_assoc]
  rw [← hprod]
  exact suslinNormal_inE_mul hX hY

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_add

theorem suslinNormal_vecMulVec_mul_of_dot {a b c d : ι → A} (h : b ⬝ᵥ c = 0) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_vecMulVec_mul_of_dot

theorem suslinNormal_vecMulVec_single_single (k l : ι) (c d : A) :
    Matrix.vecMulVec (Pi.single k c) (Pi.single l d) = Matrix.single k l (c * d) := by
  ext i j
  rw [Matrix.vecMulVec_apply]
  by_cases hi : i = k
  · by_cases hj : j = l
    · rw [hi, hj, Pi.single_eq_same, Pi.single_eq_same, Matrix.single_apply_same]
    · rw [Pi.single_eq_of_ne hj, mul_zero,
        Matrix.single_apply_of_ne k l (c * d) i j (fun h => hj h.2.symm)]
  · rw [Pi.single_eq_of_ne hi, zero_mul,
      Matrix.single_apply_of_ne k l (c * d) i j (fun h => hi h.1.symm)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_vecMulVec_single_single

theorem suslinNormal_inE_single_single (k l : ι) (c d : A) (h : k = l → c * d = 0) :
    SuslinNormalInE ι A (1 + Matrix.vecMulVec (Pi.single k c) (Pi.single l d)) := by
  rw [suslinNormal_vecMulVec_single_single]
  by_cases hkl : k = l
  · rw [h hkl, Matrix.single_zero, add_zero]
    exact suslinNormal_inE_one
  · exact ⟨elementaryUnit k l hkl (c * d), elementaryUnit_mem k l hkl (c * d), rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_single_single

theorem suslinNormal_update_add_single (z : ι → A) (l : ι) :
    z = Function.update z l 0 + Pi.single l (z l) := by
  funext m
  by_cases hm : m = l
  · rw [hm, Pi.add_apply, Function.update_self, Pi.single_eq_same, zero_add]
  · rw [Pi.add_apply, Function.update_of_ne hm, Pi.single_eq_of_ne hm, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_update_add_single

/-- Erasing the coordinate `l` keeps a vector supported in `t` once it was supported in
`insert l t`. -/
theorem suslinNormal_update_support {z : ι → A} {l : ι} {t : Finset ι}
    (hz : ∀ m, m ∉ insert l t → z m = 0) : ∀ m, m ∉ t → Function.update z l 0 m = 0 := by
  intro m hm
  by_cases hml : m = l
  · rw [hml, Function.update_self]
  · rw [Function.update_of_ne hml]
    exact hz m (fun hmem => (Finset.mem_insert.mp hmem).elim hml hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_update_support

end Transvection

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
