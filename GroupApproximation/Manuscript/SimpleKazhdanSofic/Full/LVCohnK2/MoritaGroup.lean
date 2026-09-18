import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

/-!
# Word identities for the Morita step (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  The Morita invariance
of stable `K₂` (`K₂(M_m(R)) = K₂(R)`, used by Ara–Brustenga–Cortiñas 2009 for the ultramatricial
stages of the Cohn algebra) is proved in `St_I(M_J(R))` by commutator calculus.  This file isolates
the pure group identities behind that calculus, for an arbitrary group `G`:

* `conj_eq_commutator_mul`, `conj_eq_inv_commutator_mul`: conjugation through a commutator;
* `commute_commutatorElement`: an element commuting with `a` and `b` commutes with `⁅a, b⁆`;
* `commutator_mul_left_of_commute`: `⁅a' a, z⁆ = ⁅a, z⁆ ⁅a', z⁆` when `a'` commutes with `⁅a, z⁆`;
* `commutator_switch_aux`: `⁅X, ⁅Y, Z⁆⁆ = ⁅U, Z⁆` under the switching hypotheses;
* `commutator_commutator_right_aux`, `commutator_left_commutator_aux`: conjugation of a root
  element by a "diagonal" commutator.
-/

namespace GroupApproximation.Full.LVCohnK2

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- `g h g⁻¹ = ⁅g, h⁆ h`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem conj_eq_commutator_mul (g h : G) : g * h * g⁻¹ = ⁅g, h⁆ * h := by
  group

/-- `h g h⁻¹ = ⁅g, h⁆⁻¹ g`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem conj_eq_inv_commutator_mul (g h : G) : h * g * h⁻¹ = ⁅g, h⁆⁻¹ * g := by
  group

/-- An element commuting with `a` and `b` commutes with `⁅a, b⁆`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_commutatorElement {g a b : G} (ha : Commute g a) (hb : Commute g b) :
    Commute g ⁅a, b⁆ := by
  rw [commutatorElement_def]
  exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right

/-- `⁅a' a, z⁆ = ⁅a, z⁆ ⁅a', z⁆` when `a'` commutes with `⁅a, z⁆`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_mul_left_of_commute (a a' z : G) (h : Commute a' ⁅a, z⁆) :
    ⁅a' * a, z⁆ = ⁅a, z⁆ * ⁅a', z⁆ := by
  calc ⁅a' * a, z⁆ = a' * ⁅a, z⁆ * a'⁻¹ * ⁅a', z⁆ := by group
    _ = ⁅a, z⁆ * ⁅a', z⁆ := by rw [h.eq, mul_inv_cancel_right]

/-- The switching identity: if `⁅Y, Z⁆ = V`, `X Y X⁻¹ = U Y`, and `X` commutes with `Z`, `U` with
`V`, and `V` with `Z`, then `⁅X, V⁆ = ⁅U, Z⁆`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_switch_aux (X Y Z U V : G) (hV : ⁅Y, Z⁆ = V) (hXY : X * Y * X⁻¹ = U * Y)
    (hXZ : Commute X Z) (hUV : Commute U V) (hVZ : Commute V Z) : ⁅X, V⁆ = ⁅U, Z⁆ := by
  have hVU : Commute V ⁅U, Z⁆ := commute_commutatorElement hUV.symm hVZ
  calc ⁅X, V⁆ = X * ⁅Y, Z⁆ * X⁻¹ * V⁻¹ := by rw [hV, commutatorElement_def]
    _ = ⁅X * Y * X⁻¹, X * Z * X⁻¹⁆ * V⁻¹ := by group
    _ = ⁅U * Y, Z⁆ * V⁻¹ := by rw [hXY, hXZ.eq, mul_inv_cancel_right]
    _ = U * V * U⁻¹ * ⁅U, Z⁆ * V⁻¹ := by rw [← hV]; group
    _ = V * ⁅U, Z⁆ * V⁻¹ := by rw [hUV.eq, mul_inv_cancel_right]
    _ = ⁅U, Z⁆ := by rw [hVU.eq, mul_inv_cancel_right]

/-- Conjugating a root element `Y` by `⁅X, Z⁆` from the right-hand side.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_commutator_right_aux (X Y Z P W : G) (hZY : Z⁻¹ * Y * Z = P * Y)
    (hXP : X⁻¹ * P * X = W * P) (hXY : Commute X Y) (hZW : Commute Z W) (hZP : Commute Z P)
    (hZY' : Z * Y * Z⁻¹ = P⁻¹ * Y) (hXW : Commute X W) : ⁅⁅X, Z⁆, Y⁆ = W := by
  have hY : X⁻¹ * Y * X = Y := by rw [mul_assoc, ← hXY.eq, inv_mul_cancel_left]
  have e1 : X⁻¹ * (Z⁻¹ * Y * Z) * X = W * P * Y :=
    calc X⁻¹ * (Z⁻¹ * Y * Z) * X = (X⁻¹ * P * X) * (X⁻¹ * Y * X) := by rw [hZY]; group
      _ = W * P * Y := by rw [hXP, hY]
  have e2 : Z * (W * P * Y) * Z⁻¹ = W * Y :=
    calc Z * (W * P * Y) * Z⁻¹ = (Z * W * Z⁻¹) * (Z * P * Z⁻¹) * (Z * Y * Z⁻¹) := by group
      _ = W * P * (P⁻¹ * Y) := by
        rw [hZW.eq, hZP.eq, mul_inv_cancel_right, mul_inv_cancel_right, hZY']
      _ = W * Y := by group
  have e3 : X * (W * Y) * X⁻¹ = W * Y :=
    calc X * (W * Y) * X⁻¹ = (X * W * X⁻¹) * (X * Y * X⁻¹) := by group
      _ = W * Y := by rw [hXW.eq, hXY.eq, mul_inv_cancel_right, mul_inv_cancel_right]
  calc ⁅⁅X, Z⁆, Y⁆ = X * (Z * (X⁻¹ * (Z⁻¹ * Y * Z) * X) * Z⁻¹) * X⁻¹ * Y⁻¹ := by group
    _ = W := by rw [e1, e2, e3, mul_inv_cancel_right]

/-- Conjugating `⁅X, Z⁆` by a root element `Y` from the left-hand side.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commutator_left_commutator_aux (X Y Z W T : G) (hXY : X⁻¹ * Y * X = W * Y)
    (hZY : Commute Z Y) (hZW : Z * W * Z⁻¹ = T⁻¹ * W) (hXT : Commute X T) :
    ⁅Y, ⁅X, Z⁆⁆ = T := by
  have hY : Z⁻¹ * Y * Z = Y := by rw [mul_assoc, ← hZY.eq, inv_mul_cancel_left]
  have e1 : X⁻¹ * (Z⁻¹ * Y * Z) * X = W * Y := by rw [hY, hXY]
  have e2 : Z * (W * Y) * Z⁻¹ = T⁻¹ * W * Y :=
    calc Z * (W * Y) * Z⁻¹ = (Z * W * Z⁻¹) * (Z * Y * Z⁻¹) := by group
      _ = T⁻¹ * W * Y := by rw [hZW, hZY.eq, mul_inv_cancel_right]
  have e3 : X * (T⁻¹ * W * Y) * X⁻¹ = T⁻¹ * Y :=
    calc X * (T⁻¹ * W * Y) * X⁻¹ = (X * T⁻¹ * X⁻¹) * (X * (W * Y) * X⁻¹) := by group
      _ = T⁻¹ * Y := by rw [hXT.inv_right.eq, mul_inv_cancel_right, ← hXY]; group
  calc ⁅Y, ⁅X, Z⁆⁆ = (X * (Z * (X⁻¹ * (Z⁻¹ * Y * Z) * X) * Z⁻¹) * X⁻¹ * Y⁻¹)⁻¹ := by group
    _ = T := by rw [e1, e2, e3, mul_inv_cancel_right, inv_inv]

end GroupApproximation.Full.LVCohnK2
