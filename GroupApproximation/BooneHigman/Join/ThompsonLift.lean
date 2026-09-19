import GroupApproximation.BooneHigman.Join.Rigid
import GroupApproximation.BooneHigman.Join.HigmanVCalibCore
import GroupApproximation.ThompsonOre.ThompsonShift
import Mathlib.Data.Fin.VecNotation

/-!
# Thompson's group `F` inside the all-swaps quotient of `V_2` (lane bh-pal-met-join)

Write `Q = higmanVCCommon_Q 2` and `ℓ(x, y) = jL x y`.

* `X0 = ℓ(00, 01) ℓ(01, 1) ℓ(0, 1)`.  Its boundary permutation is Thompson's `x_0`, which maps
  `0 ↦ 00`, `10 ↦ 01`, `11 ↦ 1` (`mapsCone_X0_zero`, `_one_zero`, `_one_one`).
* `Y n = jPhi (1ⁿ) X0`, so `Y 0 = X0` and `Y 1 = X1` is Thompson's `x_1`.
* By rigid conjugation (`rcl_phi`), `X0⁻¹ Y (n + 1) X0 = Y (n + 2)` (`conj_X0_Y`), and more
  generally `Y m⁻¹ Y n Y m = Y (n + 1)` for `m < n` (`conj_Y_Y`).
* Hence Guba's two relations hold, and `psi : ThompsonF →* Q` sends `x0 ↦ X0`, `x1 ↦ X1`.
  It maps `xn n ↦ Y n` (`psi_xn`) and intertwines the shift with `jPhi [1]` (`psi_shift`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope
open GroupApproximation.ThompsonOre

theorem jd2 : 1 < 2 := by norm_num

#audit_axioms GroupApproximation.BooneHigman.Join.jd2

/-- The lift of Thompson's `x_0`. -/
noncomputable def X0 : higmanVCCommon_Q 2 :=
  jL [0, 0] [0, 1] * jL [0, 1] [1] * jL [0] [1]

#audit_axioms GroupApproximation.BooneHigman.Join.X0

/-- The boundary permutation of `X0` as a product of three cone swaps. -/
theorem jperm_X0 : jperm 2 X0 =
    coneSwap [0, 0] [0, 1] (by decide) (by decide) * coneSwap [0, 1] [1] (by decide) (by decide) *
      coneSwap [0] [1] (by decide) (by decide) := by
  unfold X0
  rw [jperm_mul, jperm_mul, jperm_jL (d := 2) (x := [0, 0]) (y := [0, 1]) (by decide) (by decide),
    jperm_jL (d := 2) (x := [0, 1]) (y := [1]) (by decide) (by decide),
    jperm_jL (d := 2) (x := [0]) (y := [1]) (by decide) (by decide)]

#audit_axioms GroupApproximation.BooneHigman.Join.jperm_X0

theorem mapsCone_X0_zero : MapsCone (jperm 2 X0) [0] [0, 0] := by
  rw [jperm_X0]
  exact MapsCone.comp (mapsCone_coneSwap_left _ _)
    (MapsCone.comp (mapsCone_coneSwap_right _ _) (mapsCone_coneSwap_right _ _))

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_X0_zero

theorem mapsCone_X0_one_zero : MapsCone (jperm 2 X0) [1, 0] [0, 1] := by
  rw [jperm_X0]
  exact MapsCone.comp ((mapsCone_coneSwap_right (v := [0]) (w := [1]) _ _).append [0])
    (MapsCone.comp (mapsCone_coneSwap_fix (x := [0, 0]) _ _ (by decide) (by decide) (by decide)
      (by decide)) (mapsCone_coneSwap_left _ _))

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_X0_one_zero

theorem mapsCone_X0_one_one : MapsCone (jperm 2 X0) [1, 1] [1] := by
  rw [jperm_X0]
  exact MapsCone.comp ((mapsCone_coneSwap_right (v := [0]) (w := [1]) _ _).append [1])
    (MapsCone.comp (mapsCone_coneSwap_left _ _)
      (mapsCone_coneSwap_fix (x := [1]) _ _ (by decide) (by decide) (by decide) (by decide)))

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_X0_one_one

theorem mapsCone_X0inv_one : MapsCone (jperm 2 X0⁻¹) [1] [1, 1] := by
  rw [jperm_inv]
  exact mapsCone_X0_one_one.inv

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_X0inv_one

/-- The lifts `Y n = jPhi (1ⁿ) X0` of Thompson's `x_n`. -/
noncomputable def Y (n : ℕ) : higmanVCCommon_Q 2 :=
  jPhi 2 (List.replicate n 1) X0

#audit_axioms GroupApproximation.BooneHigman.Join.Y

theorem Y_zero : Y 0 = X0 := by
  unfold Y
  rw [List.replicate_zero, jPhi_nil']

#audit_axioms GroupApproximation.BooneHigman.Join.Y_zero

theorem jPhi_one_Y (n : ℕ) : jPhi 2 [1] (Y n) = Y (n + 1) := by
  unfold Y
  rw [jPhi_append]
  all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_one_Y

theorem jPhi_rep_Y (m n : ℕ) : jPhi 2 (List.replicate m 1) (Y n) = Y (n + m) := by
  unfold Y
  rw [jPhi_append, List.replicate_append_replicate, Nat.add_comm]

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_rep_Y

/-- `X0⁻¹ · jPhi [1] r · X0 = jPhi [1, 1] r`. -/
theorem conj_X0_phi_one (r : higmanVCCommon_Q 2) :
    X0⁻¹ * jPhi 2 [1] r * X0 = jPhi 2 [1, 1] r := by
  have h := rcl_phi jd2 X0⁻¹ mapsCone_X0inv_one r
  rwa [inv_inv] at h

#audit_axioms GroupApproximation.BooneHigman.Join.conj_X0_phi_one

theorem jPhi_one_one_Y (n : ℕ) : jPhi 2 [1, 1] (Y n) = Y (n + 2) := by
  unfold Y
  rw [jPhi_append]
  all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_one_one_Y

theorem conj_X0_Y (n : ℕ) : X0⁻¹ * Y (n + 1) * X0 = Y (n + 2) := by
  rw [← jPhi_one_Y n, conj_X0_phi_one, jPhi_one_one_Y]

#audit_axioms GroupApproximation.BooneHigman.Join.conj_X0_Y

/-- `Y m⁻¹ · Y n · Y m = Y (n + 1)` for `m < n`. -/
theorem conj_Y_Y (m k : ℕ) : (Y m)⁻¹ * Y (m + k + 1) * Y m = Y (m + k + 2) := by
  have e1 : Y m = jPhi 2 (List.replicate m 1) (Y 0) := by rw [jPhi_rep_Y, Nat.zero_add]
  have e2 : Y (m + k + 1) = jPhi 2 (List.replicate m 1) (Y (k + 1)) := by
    rw [jPhi_rep_Y]
    congr 1
    omega
  have e3 : Y (m + k + 2) = jPhi 2 (List.replicate m 1) (Y (k + 2)) := by
    rw [jPhi_rep_Y]
    congr 1
    omega
  rw [e1, e2, e3, ← map_inv, ← map_mul, ← map_mul, Y_zero, conj_X0_Y]

#audit_axioms GroupApproximation.BooneHigman.Join.conj_Y_Y

theorem rel_one_Q : (X0 ^ 2)⁻¹ * Y 1 * X0 ^ 2 = (X0 * Y 1)⁻¹ * Y 1 * (X0 * Y 1) := by
  have c1 : X0⁻¹ * Y 1 * X0 = Y 2 := conj_X0_Y 0
  have c2 : X0⁻¹ * Y 2 * X0 = Y 3 := conj_X0_Y 1
  have d1 : (Y 1)⁻¹ * Y 2 * Y 1 = Y 3 := conj_Y_Y 1 0
  calc (X0 ^ 2)⁻¹ * Y 1 * X0 ^ 2 = X0⁻¹ * (X0⁻¹ * Y 1 * X0) * X0 := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    _ = Y 3 := by rw [c1, c2]
    _ = (Y 1)⁻¹ * (X0⁻¹ * Y 1 * X0) * Y 1 := by rw [c1, d1]
    _ = (X0 * Y 1)⁻¹ * Y 1 * (X0 * Y 1) := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Join.rel_one_Q

theorem rel_two_Q : (X0 ^ 3)⁻¹ * Y 1 * X0 ^ 3 = (X0 ^ 2 * Y 1)⁻¹ * Y 1 * (X0 ^ 2 * Y 1) := by
  have c1 : X0⁻¹ * Y 1 * X0 = Y 2 := conj_X0_Y 0
  have c2 : X0⁻¹ * Y 2 * X0 = Y 3 := conj_X0_Y 1
  have c3 : X0⁻¹ * Y 3 * X0 = Y 4 := conj_X0_Y 2
  have d2 : (Y 1)⁻¹ * Y 3 * Y 1 = Y 4 := conj_Y_Y 1 1
  calc (X0 ^ 3)⁻¹ * Y 1 * X0 ^ 3 = X0⁻¹ * (X0⁻¹ * (X0⁻¹ * Y 1 * X0) * X0) * X0 := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    _ = Y 4 := by rw [c1, c2, c3]
    _ = (Y 1)⁻¹ * (X0⁻¹ * (X0⁻¹ * Y 1 * X0) * X0) * Y 1 := by rw [c1, c2, d2]
    _ = (X0 ^ 2 * Y 1)⁻¹ * Y 1 * (X0 ^ 2 * Y 1) := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Join.rel_two_Q

/-- The images of Guba's generators. -/
noncomputable def psiGen : Fin 2 → higmanVCCommon_Q 2 := ![X0, Y 1]

#audit_axioms GroupApproximation.BooneHigman.Join.psiGen

/-- **The lift of Thompson's group `F`** into the all-swaps quotient of `V_2`. -/
noncomputable def psi : ThompsonF →* higmanVCCommon_Q 2 :=
  PresentedGroup.toGroup (lift_thompsonRels psiGen rel_one_Q rel_two_Q)

#audit_axioms GroupApproximation.BooneHigman.Join.psi

theorem psi_x0 : psi x0 = X0 :=
  PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigman.Join.psi_x0

theorem psi_x1 : psi x1 = Y 1 :=
  PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigman.Join.psi_x1

theorem conj_X0pow_Y1 (n : ℕ) : (X0 ^ n)⁻¹ * Y 1 * X0 ^ n = Y (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (X0 ^ (n + 1))⁻¹ * Y 1 * X0 ^ (n + 1) =
        X0⁻¹ * ((X0 ^ n)⁻¹ * Y 1 * X0 ^ n) * X0 := by
      rw [pow_succ]
      group
    rw [e, ih]
    exact conj_X0_Y n

#audit_axioms GroupApproximation.BooneHigman.Join.conj_X0pow_Y1

theorem psi_xn (n : ℕ) : psi (xn n) = Y n := by
  cases n with
  | zero => rw [xn_zero, psi_x0, Y_zero]
  | succ n =>
    rw [xn_succ, map_mul, map_mul, map_inv, map_pow, psi_x0, psi_x1]
    exact conj_X0pow_Y1 n

#audit_axioms GroupApproximation.BooneHigman.Join.psi_xn

/-- `psi` intertwines the shift of `F` with the prefix endomorphism `jPhi [1]`. -/
theorem psi_shift (g : ThompsonF) : psi (shift g) = jPhi 2 [1] (psi g) := by
  have h : psi.comp shift = (jPhi 2 [1]).comp psi := by
    refine PresentedGroup.ext fun i => ?_
    show psi (shift (PresentedGroup.of i)) = jPhi 2 [1] (psi (PresentedGroup.of i))
    rw [shift_of, ← xn_of, psi_xn, psi_xn, jPhi_one_Y]
  exact DFunLike.congr_fun h g

#audit_axioms GroupApproximation.BooneHigman.Join.psi_shift

end GroupApproximation.BooneHigman.Join
