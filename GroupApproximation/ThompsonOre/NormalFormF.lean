/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.ThompsonOre.NormalFormExists
import GroupApproximation.ThompsonOre.ShiftOreBrown
import GroupApproximation.ThompsonOre.ThompsonShift
import Mathlib.Data.Fin.VecNotation

/-!
# The normal form of Thompson's group `F` (the presented group `ThompsonF`)

`thompsonFModel` is the `FModel` on `ThompsonF`:
- the generators are Guba's `xn`;
- the relations and generation come from Brown's positive frame, transported along
  `thompsonEquivBrown` (`thompsonFrame`);
- the shift is `ThompsonOre.shift`, which is injective through the faithful action on `ℚ`;
- `chiF` is the `x_0`-exponent, defined from the presentation.

Main results:
* `thompsonF_nf_exists`: every `g : ThompsonF` is `x_0^{a_0} ⋯ x_n^{a_n} x_n^{-b_n} ⋯ x_0^{-b_0}` for a
  normal form `[(a_0, b_0), …, (a_n, b_n)]` (`thompsonF_val_eq`);
* `thompsonF_nf_unique`: two normal forms with the same value are equal;
* `thompsonF_nf_existsUnique`: both together.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

open FNormal HigmanThompson

noncomputable section

/-- Brown's positive frame, moved to `ThompsonF`. -/
def thompsonFrame : PositiveFrame ThompsonF := brownFrame.map thompsonEquivBrown.symm

theorem thompsonFrame_x (i : ℕ) : thompsonFrame.x i = xn i := by
  show thompsonEquivBrown.symm (brownX 0 i)⁻¹ = xn i
  rw [map_inv, thompsonEquivBrown_symm_apply, fromBrown_X, inv_inv]

/-- The `x_0`-exponent of `F`: `x_0 ↦ 1`, `x_1 ↦ 0`. -/
def chiF : ThompsonF →* Multiplicative ℤ :=
  PresentedGroup.toGroup
    (lift_thompsonRels ![Multiplicative.ofAdd 1, 1] (by simp) (by simp))

theorem chiF_x0 : chiF x0 = Multiplicative.ofAdd 1 := by
  show PresentedGroup.toGroup _ (PresentedGroup.of 0) = _
  rw [PresentedGroup.toGroup.of]
  simp

theorem chiF_x1 : chiF x1 = 1 := by
  show PresentedGroup.toGroup _ (PresentedGroup.of 1) = _
  rw [PresentedGroup.toGroup.of]
  simp

theorem chiF_xn_succ (n : ℕ) : chiF (xn (n + 1)) = 1 := by
  rw [xn_succ, map_mul, map_mul, map_inv, chiF_x1, mul_one, inv_mul_cancel]

/-- The model of `F` given by `ThompsonF`. -/
def thompsonFModel : FModel ThompsonF where
  x := xn
  rel i j h := by
    have h1 := thompsonFrame.rel i j h
    simpa only [thompsonFrame_x] using h1
  closure_eq_top := by
    have hx : thompsonFrame.x = xn := funext thompsonFrame_x
    rw [← hx]
    exact thompsonFrame.closure_eq_top
  shift := GroupApproximation.ThompsonOre.shift
  shift_x := shift_xn
  shift_injective := GroupApproximation.ThompsonOre.shift_injective
  chi := chiF
  chi_x_zero := chiF_x0
  chi_x_succ := chiF_xn_succ

@[simp] theorem thompsonFModel_x (n : ℕ) : thompsonFModel.x n = xn n := rfl

/-- **Existence of the normal form in `F`.** -/
theorem thompsonF_nf_exists (g : ThompsonF) : ∃ l, IsNF l ∧ thompsonFModel.val l = g :=
  thompsonFModel.nf_exists g

/-- **Uniqueness of the normal form in `F`.** -/
theorem thompsonF_nf_unique {l l' : List (ℕ × ℕ)} (hl : IsNF l) (hl' : IsNF l')
    (h : thompsonFModel.val l = thompsonFModel.val l') : l = l' :=
  thompsonFModel.nf_unique l l' hl hl' h

/-- **The normal form of `F`**: every element has exactly one. -/
theorem thompsonF_nf_existsUnique (g : ThompsonF) : ∃! l, IsNF l ∧ thompsonFModel.val l = g :=
  thompsonFModel.nf_existsUnique g

/-- The value of a form is the standard product `x_0^{a_0} ⋯ x_n^{a_n} · (x_0^{b_0} ⋯ x_n^{b_n})⁻¹`
in Guba's generators. -/
theorem thompsonF_val_eq (l : List (ℕ × ℕ)) :
    thompsonFModel.val l = thompsonFModel.posWord 0 l * (thompsonFModel.negWord 0 l)⁻¹ :=
  thompsonFModel.val_eq_pos_mul_inv l

end

end GroupApproximation.ThompsonOre
