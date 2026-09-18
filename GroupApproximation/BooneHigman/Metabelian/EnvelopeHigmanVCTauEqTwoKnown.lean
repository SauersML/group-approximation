import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommOptions
import GroupApproximation.Meta.AxiomGuard

/-!
# Instances known at level `n` (lane bh-met-91q)

Fix a level `n` with the induction hypotheses `higmanVCTauShort_Below d n` and
`higmanVCTauShort_Shrink d n`.  An instance `(s; A → B)` (`s = (p, q)`, `A = (x, y)`,
`B = (x', y')`) is **known at level `n`** (`higmanVCTauEqTwo_Known`) if
* one side is below level `n` and the other at most level `n` (Shrink, read either way); or
* all four words are short (an all-short relator); or
* both sides are at level `n` and one side has Option A, Option E, Option R, flexible A or
  flexible B (`higmanVCTauEqTwo_Opt`).

`higmanVCTauEqTwo_inst_of_known`: a known instance holds.  This packages the case lemmas of
lanes bh-met-77j and bh-met-77m (`higmanVCTauShort_square`, `higmanVCTauShort_optionE`,
`higmanVCTauComm_erev`, `higmanVCTauComm_flexA_case`, `higmanVCTauComm_flexB_case`) so that
they can be used on the three sub-instances of a decomposition
(`EnvelopeHigmanVCTauEqTwoSquare`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- One of the five level-`n` options on the side `(x, y)` of `(s; (x, y) → (x', y'))`. -/
def higmanVCTauEqTwo_Opt (d : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  (∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p), higmanVCTauShort_OptionA d p q x y hpq hqp) ∨
    higmanVCTauShort_OptionE d p q x y ∨ higmanVCTauComm_OptionR d p q x y ∨
    (∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p), higmanVCTauComm_FlexA d p q x y hpq hqp) ∨
    higmanVCTauComm_FlexB d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_Opt

/-- **Known at level `n`.** -/
def higmanVCTauEqTwo_Known (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  (x.length + y.length < n ∧ x'.length + y'.length ≤ n) ∨
    (x'.length + y'.length < n ∧ x.length + y.length ≤ n) ∨
    (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) ∨
    (x.length + y.length = n ∧ x'.length + y'.length = n ∧
      (higmanVCTauEqTwo_Opt d p q x y x' y' ∨ higmanVCTauEqTwo_Opt d p q x' y' x y))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_Known

/-- A cone swap carries incomparable words to incomparable words. -/
theorem higmanVCTauEqTwo_inc {d : ℕ} (hd : 1 < d) {v w x y X Y : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hx : MapsCone (coneSwap v w hvw hwv) x X)
    (hy : MapsCone (coneSwap v w hvw hwv) y Y) (hxy : ¬ x <+: y) : ¬ X <+: Y := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hss := coneSwap_mul_self hvw hwv
  exact higmanVCTauConj_not_prefix_of_maps (higmanVCTauConj_mapsCone_symm hx hss)
    (higmanVCTauConj_mapsCone_symm hy hss) hxy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_inc

/-- **An option at the top level** (`|x| + |y| = n`, `|x'| + |y'| ≤ n`). -/
theorem higmanVCTauEqTwo_opt_at {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hA : x.length + y.length = n)
    (hBn : x'.length + y'.length ≤ n) (hO : higmanVCTauEqTwo_Opt d p q x y x' y') :
    higmanVCTauShort_Inst d p q x y x' y' := by
  unfold higmanVCTauShort_Inst
  intro hpq hqp hp hq hmx hmy hxy hyx hxy' hyx'
  unfold higmanVCTauEqTwo_Opt at hO
  rcases hO with ⟨_, _, hOA⟩ | hE | hR | ⟨_, _, hF⟩ | hF
  · unfold higmanVCTauShort_OptionA at hOA
    obtain ⟨hlong, P', Q', X', Y', hP, hQ, hP3, hQ3, hX, hY, hlt⟩ := hOA
    have hC := higmanVCTauConj_len_lt hd hlong hxy hyx
    have e1 := hB p q (higmanVCTau_pX (x, y)) (higmanVCTau_pY (x, y)) X' Y'
      (by omega) (by omega)
    have e2 : higmanVCTauShort_Inst d P' Q' X' Y' x' y' :=
      hS P' Q' X' Y' x' y' (by omega) hBn
    exact higmanVCTauShort_square hd hpq hqp hp hq hlong hmx hmy hxy hyx hxy' hyx' hP hQ hP3
      hQ3 hX hY e1 e2
  · exact higmanVCTauShort_optionE hd hpq hqp hE hxy hyx hmx hmy
  · unfold higmanVCTauComm_OptionR at hR
    obtain ⟨hlong, rfl, rfl⟩ := hR
    exact higmanVCTauComm_erev hd hlong hpq hqp hxy hyx hmx hmy
  · exact higmanVCTauComm_flexA_case hd hB hS hpq hqp hp hq hA hBn hF hmx hmy hxy hyx hxy'
      hyx'
  · exact higmanVCTauComm_flexB_case hd hB hS hpq hqp hp hq hA hBn hF hmx hmy hxy hyx hxy'
      hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_opt_at

/-- **A known instance holds.** -/
theorem higmanVCTauEqTwo_inst_of_known {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hK : higmanVCTauEqTwo_Known d n p q x y x' y') :
    higmanVCTauShort_Inst d p q x y x' y' := by
  unfold higmanVCTauEqTwo_Known at hK
  rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hs | ⟨h1, h2, hO | hO⟩
  · exact hS p q x y x' y' h1 h2
  · exact higmanVCTauShort_symm (hS p q x' y' x y h1 h2)
  · unfold higmanVCTauShort_Inst
    intro hpq hqp hp hq hmx hmy hxy hyx hxy' hyx'
    exact higmanVCTauShort_allShort hd hpq hqp hp hq hs hmx hmy hxy hyx hxy' hyx'
  · exact higmanVCTauEqTwo_opt_at hd hB hS h1 h2.le hO
  · exact higmanVCTauShort_symm (higmanVCTauEqTwo_opt_at hd hB hS h2 h1.le hO)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_inst_of_known

end GroupApproximation.BooneHigman.Metabelian.Envelope
