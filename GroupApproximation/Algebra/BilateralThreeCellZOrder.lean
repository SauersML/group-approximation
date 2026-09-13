import GroupApproximation.Algebra.BilateralThreeCellMatrices
import GroupApproximation.Dynamics.BilateralThreeCellClopen
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsMatrixUnits
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.CharP.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:bilateral-three`: `⟨z⟩` is a nontrivial finite central subgroup of order `char(k)`

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three`
(`\label{prop:bilateral-three}`, tex 1583–1587 at origin/main 8547915b2):

> Hence $z\in\mathfrak D_B(L)$.  It commutes with $L$, since both its supports lie outside $P$;
> with $W$, since its two levels are fixed; and with $c,y$, by the matrix-unit products.  So
> $\langle z\rangle$ is a nontrivial finite central subgroup of $B$, of order
> $\operatorname{char}(k)$.

`BilateralThreeCellStatement` records only `IsOfFinOrder z`.  This module proves the whole printed
clause for the cell of a compressed clopen `P` with nonempty defect `D = P∖T(P)` over a finite
field `k`:

* for every cell, `z^m = 1 + E₃₃(m f_{-1,-2})`, so `z^m = 1` exactly when `m d = 0`
  (`ZOrder.z_pow_eq_one_iff`);
* in `R_X`, `m d = m·1_D = 0` exactly when `char k ∣ m`, because `D` is nonempty
  (`ClopenCrossedProduct.nsmul_defectD_eq_zero_iff`);
* so `orderOf z = char k` and `z ≠ 1`.  With `z ∈ B` and `z` central in `B`
  (`Cell.z_mem_B`, `Cell.z_commute_B`), this is `PrintedBilateralThreeZCentralOfOrderChar`.
-/

namespace GroupApproximation
namespace BilateralThreeCell
namespace ZOrder

variable {R : Type*} [Ring R] (C : Cell R)

/-- `z^m = 1 + E₃₃(m f_{-1,-2})`: `E₃₃ f_{-1,-2}` squares to zero. -/
theorem z_pow_val (m : ℕ) :
    ((C.z ^ m : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) =
      1 + Matrix.single (2 : Fin 3) (2 : Fin 3) (m • C.f (-1) (-2)) := by
  rw [Units.val_pow_eq_pow_val]
  change (1 + Matrix.single (2 : Fin 3) (2 : Fin 3) (C.f (-1) (-2))) ^ m = _
  rw [Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.one_add_pow_of_sq_zero
      (single_mul_single_eq_zero (Or.inr C.f_mul_self_neg_one_neg_two)) m,
    Matrix.smul_single]

/-- `z^m = 1` exactly when `m f_{-1,-2} = 0`. -/
theorem z_pow_eq_one_iff_nsmul_f (m : ℕ) : C.z ^ m = 1 ↔ m • C.f (-1) (-2) = 0 := by
  constructor
  · intro h
    have h1 : (1 : Matrix (Fin 3) (Fin 3) R) +
        Matrix.single (2 : Fin 3) (2 : Fin 3) (m • C.f (-1) (-2)) = 1 + 0 := by
      rw [← z_pow_val C m, h, Units.val_one, add_zero]
    have hA : Matrix.single (2 : Fin 3) (2 : Fin 3) (m • C.f (-1) (-2)) = 0 :=
      add_left_cancel h1
    have h2 := congrFun (congrFun hA 2) 2
    simpa using h2
  · intro h
    apply Units.ext
    rw [z_pow_val C m, Units.val_one]
    simp [h]

/-- `m f_{-1,-2} = u^{-1}(m d)u²`. -/
theorem nsmul_f_eq (m : ℕ) : m • C.f (-1) (-2) = C.pw (-1) * (m • C.d) * C.pw 2 := by
  rw [Cell.f, neg_neg, mul_smul_comm, smul_mul_assoc]

/-- `m f_{-1,-2} = 0` exactly when `m d = 0`: `f_{-1,-2}` is `d` conjugated by units. -/
theorem nsmul_f_eq_zero_iff (m : ℕ) : m • C.f (-1) (-2) = 0 ↔ m • C.d = 0 := by
  rw [nsmul_f_eq C m]
  constructor
  · intro h
    have h2 : C.pw 1 * (C.pw (-1) * (m • C.d) * C.pw 2) * C.pw (-2) = m • C.d := by
      rw [← mul_assoc, ← mul_assoc, C.pw_mul_pw_neg 1, one_mul, mul_assoc, C.pw_mul_pw_neg 2,
        mul_one]
    rw [← h2, h, mul_zero, zero_mul]
  · intro h
    rw [h, mul_zero, zero_mul]

/-- **`z^m = 1` exactly when `m d = 0`**, for every cell. -/
theorem z_pow_eq_one_iff (m : ℕ) : C.z ^ m = 1 ↔ m • C.d = 0 :=
  (z_pow_eq_one_iff_nsmul_f C m).trans (nsmul_f_eq_zero_iff C m)

end ZOrder
end BilateralThreeCell

namespace ClopenCrossedProduct

open BilateralThreeCell

section Field

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Field k] {P : Set X}

/-- **`m·1_D = 0` in `R_X` exactly when `char k ∣ m`**, for nonempty `D = P∖T(P)`. -/
theorem nsmul_defectD_eq_zero_iff (hP : IsClopen P) {x : X} (hx : x ∈ P \ T '' P) (m : ℕ) :
    m • defectD T k hP = 0 ↔ ringChar k ∣ m := by
  rw [← ringChar.spec (R := k) m]
  constructor
  · intro h
    rw [defectD, ← map_nsmul, ← map_zero (coeff T k)] at h
    have h2 := congrArg (fun f : LocallyConstant X k => f x) (coeff_injective T k h)
    change m • (LocallyConstant.charFn k (hP.diff (isClopen_image T hP))) x = 0 at h2
    rw [LocallyConstant.coe_charFn, Set.indicator_of_mem hx, Pi.one_apply, nsmul_eq_mul,
      mul_one] at h2
    exact h2
  · intro h
    have h0 : m • LocallyConstant.charFn k (hP.diff (isClopen_image T hP)) = 0 := by
      ext y
      change m • (LocallyConstant.charFn k (hP.diff (isClopen_image T hP))) y = 0
      rw [nsmul_eq_mul, h, zero_mul]
    rw [defectD, ← map_nsmul, h0, map_zero]

/-- **`z^m = 1` exactly when `char k ∣ m`**, for the cell of a compressed clopen `P` with
nonempty defect. -/
theorem bilateralCell_z_pow_eq_one_iff (hP : IsClopen P) (hTP : T '' P ⊆ P) {x : X}
    (hx : x ∈ P \ T '' P) (m : ℕ) :
    (bilateralCell T k hP hTP).z ^ m = 1 ↔ ringChar k ∣ m := by
  rw [ZOrder.z_pow_eq_one_iff, bilateralCell_d, nsmul_defectD_eq_zero_iff T k hP hx]

/-- **"of order `char(k)`"** (tex 1586–1587). -/
theorem bilateralCell_orderOf_z (hP : IsClopen P) (hTP : T '' P ⊆ P) {x : X}
    (hx : x ∈ P \ T '' P) :
    orderOf (bilateralCell T k hP hTP).z = ringChar k :=
  Nat.dvd_antisymm
    (orderOf_dvd_iff_pow_eq_one.mpr ((bilateralCell_z_pow_eq_one_iff T k hP hTP hx _).mpr dvd_rfl))
    ((bilateralCell_z_pow_eq_one_iff T k hP hTP hx _).mp (pow_orderOf_eq_one _))

/-- **"nontrivial"** (tex 1586): `z ≠ 1`. -/
theorem bilateralCell_z_ne_one (hP : IsClopen P) (hTP : T '' P ⊆ P) {x : X}
    (hx : x ∈ P \ T '' P) :
    (bilateralCell T k hP hTP).z ≠ 1 := by
  intro h
  have h1 : ringChar k ∣ 1 :=
    (bilateralCell_z_pow_eq_one_iff T k hP hTP hx 1).mp (by rw [h, one_pow])
  have h2 : ((1 : ℕ) : k) = 0 := (ringChar.spec (R := k) 1).mpr h1
  rw [Nat.cast_one] at h2
  exact one_ne_zero h2

end Field

/-- **Printed (tex 1585–1587):** "So `⟨z⟩` is a nontrivial finite central subgroup of `B`, of
order `char(k)`."

Standing data of the proof of `prop:bilateral-three` (tex 1550–1574): a clopen `P` with
`T(P) ⊆ P` and nonempty `D = P∖T(P)`, a finite field `k`, the cell `bilateralCell T k hP hTP`
(`u` the implementing unit, `p = 1_P`), and `B = ⟨L, W, c, y⟩` with `L` the elementary group over a
coefficient set `S ⊆ pR_Xp` containing `p` (`Cell.B S`; the printed `S` is one such set).  "Central"
is spelled as commuting with every element of `B`. -/
def PrintedBilateralThreeZCentralOfOrderChar : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Field k] [Finite k]
    (P : Set X) (hP : IsClopen P) (hTP : T '' P ⊆ P), (P \ T '' P).Nonempty →
      ∀ S : Set (ClopenCrossedProduct T k),
        (∀ a ∈ S, (bilateralCell T k hP hTP).p * a * (bilateralCell T k hP hTP).p = a) →
        (bilateralCell T k hP hTP).p ∈ S →
          (bilateralCell T k hP hTP).z ∈ (bilateralCell T k hP hTP).B S ∧
            (∀ g ∈ (bilateralCell T k hP hTP).B S, Commute (bilateralCell T k hP hTP).z g) ∧
            Subgroup.zpowers (bilateralCell T k hP hTP).z ≠ ⊥ ∧
            (Subgroup.zpowers (bilateralCell T k hP hTP).z :
              Set (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T k))ˣ).Finite ∧
            Nat.card ↥(Subgroup.zpowers (bilateralCell T k hP hTP).z) = ringChar k ∧
            orderOf (bilateralCell T k hP hTP).z = ringChar k

/-- Closed proof of the printed clause. -/
theorem manuscriptSentence_bilateralThreeZCentralOfOrderChar :
    PrintedBilateralThreeZCentralOfOrderChar := by
  rintro X _ T k _ _ P hP hTP ⟨x, hx⟩ S hS hp
  have hord := bilateralCell_orderOf_z T k hP hTP hx
  refine ⟨(bilateralCell T k hP hTP).z_mem_B hp, (bilateralCell T k hP hTP).z_commute_B hS,
    ?_, ?_, ?_, hord⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact bilateralCell_z_ne_one T k hP hTP hx
  · refine finite_zpowers.mpr (orderOf_pos_iff.mp ?_)
    rw [hord]
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (R := k) (ringChar k))
  · rw [Nat.card_zpowers, hord]

end ClopenCrossedProduct
end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.manuscriptSentence_bilateralThreeZCentralOfOrderChar
#audit_axioms GroupApproximation.BilateralThreeCell.ZOrder.z_pow_eq_one_iff
#audit_axioms GroupApproximation.ClopenCrossedProduct.bilateralCell_orderOf_z
