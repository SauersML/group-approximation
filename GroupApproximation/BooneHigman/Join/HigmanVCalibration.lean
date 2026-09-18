import GroupApproximation.BooneHigman.Join.HigmanVCalibCore
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonPush

/-!
# The Thompson-`F` calibration identity in the all-swaps quotient `Q` of `V_2`
(lane bh-pal-met-join)

This file instantiates `calib_of_relators` (`Join/HigmanVCalibCore.lean`) with the letters of
`higmanVCCommon_Q 2`, the all-swaps free group modulo the standard relators `higmanVC_rels`.
It shows that in `Q`,
`(0, 10) (0, 1000) = (00, 10) (00, 1000) (01, 101) (01, 1001)`.

The left side is the hard Step-B core instance from
`research/higman-v-step-b-core-local-conjugation-and-f-obstruction.md` (Claim C). Its
evaluation in `V_2` has infinite order.  The right side is `(00, 10)` times an element of the
antichain subgroup on `{00, 01, 1000, 1001, 101, 11}`.  So this instance lies in
`S = U · ⋃ H_C · U`, and no Higman input is used.
-/

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The class in `Q` of the letter `(x, y)`. -/
noncomputable def qLetter (x y : List (Fin 2)) : higmanVCCommon_Q 2 :=
  higmanVCCommon_mk 2 (FreeGroup.of (x, y))

#audit_axioms GroupApproximation.BooneHigman.Join.qLetter

theorem qLetter_sq (x y : List (Fin 2)) : qLetter x y * qLetter x y = 1 :=
  higmanVCCommon_mk_sq x y

#audit_axioms GroupApproximation.BooneHigman.Join.qLetter_sq

/-- The conjugation relator in `Q`. -/
theorem qLetter_conj {p q x y x' y' : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    qLetter p q * qLetter x y * (qLetter p q)⁻¹ = qLetter x' y' := by
  have h := higmanVCCommon_mk_rel (higmanVCCommon_conj_mem hpq hqp hmx hmy hxy hyx hxy' hyx')
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
  exact mul_inv_eq_one.mp h

#audit_axioms GroupApproximation.BooneHigman.Join.qLetter_conj

/-- The split relator in `Q`, for `d = 2`. -/
theorem qLetter_split {x y : List (Fin 2)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    qLetter x y = qLetter (x ++ [0]) (y ++ [0]) * qLetter (x ++ [1]) (y ++ [1]) := by
  unfold qLetter
  rw [higmanVCCommon_mk_split h1 h2, higmanVC_splitAll]
  have hr : List.finRange 2 = [0, 1] := by first | decide | rfl | simp [List.finRange]
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Join.qLetter_split

/-- **The calibration identity in `Q`.** -/
theorem qLetter_calibration :
    qLetter [0] [1, 0] * qLetter [0] [1, 0, 0, 0] =
      qLetter [0, 0] [1, 0] * qLetter [0, 0] [1, 0, 0, 0] * qLetter [0, 1] [1, 0, 1] *
        qLetter [0, 1] [1, 0, 0, 1] :=
  calib_of_relators qLetter qLetter_sq qLetter_conj qLetter_split

#audit_axioms GroupApproximation.BooneHigman.Join.qLetter_calibration

end GroupApproximation.BooneHigman.Join
