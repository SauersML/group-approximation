import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDeepHop
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop C with deep legs (lane bh-met-77t)

`higmanVCTauDeep_HopCD` is Hop C of lane bh-met-77r (`higmanVCTauLevel_HopC`, conjugated
conjugator) whose three legs `(r; A → A1)`, `(s1; A1 → B1)`, `(r; B1 → B)` are only deep legs
(`higmanVCTauDeep_DLeg`: a leg, or Hop D from either side) instead of easy instances.
`higmanVCTauDeep_hopCD_case` proves it exactly as `higmanVCTauLevel_hopC_case`, with
`higmanVCTauDeep_dleg` in place of `higmanVCTauLevel_easy`.

Example (scratch `SP/bh-met-77t/deep2.py`, `d = 2`): `A = (0, 1000)`, `s = (100, 111)`,
`r = (100, 101)`, `s1 = r(s) = (101, 111)`; here `(s1; A1 → B1)` is a Hop D instance.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Hop CD**: Hop C whose three legs are deep legs. -/
def higmanVCTauDeep_HopCD (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ∃ (R S p1 q1 x1 y1 x2 y2 : List (Fin d)) (hRS : ¬ R <+: S) (hSR : ¬ S <+: R),
    R.length ≤ 3 ∧ S.length ≤ 3 ∧
    MapsCone (coneSwap R S hRS hSR) p p1 ∧ MapsCone (coneSwap R S hRS hSR) q q1 ∧
    p1.length ≤ 3 ∧ q1.length ≤ 3 ∧
    MapsCone (coneSwap R S hRS hSR) x x1 ∧ MapsCone (coneSwap R S hRS hSR) y y1 ∧
    MapsCone (coneSwap R S hRS hSR) x' x2 ∧ MapsCone (coneSwap R S hRS hSR) y' y2 ∧
    higmanVCTauDeep_DLeg d n R S x y x1 y1 ∧ higmanVCTauDeep_DLeg d n p1 q1 x1 y1 x2 y2 ∧
    higmanVCTauDeep_DLeg d n R S x2 y2 x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_HopCD

/-- **Hop CD case**, conjugated conjugator with deep legs, from the level-`n` hypotheses. -/
theorem higmanVCTauDeep_hopCD_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hH : higmanVCTauDeep_HopCD d n p q x y x' y')
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨R, S, p1, q1, x1, y1, x2, y2, hRS, hSR, hR, hS3, hrp, hrq, hp1, hq1, hrx, hry,
    hrx', hry', hE1, hE2, hE3⟩ := hH
  have hrr := coneSwap_mul_self hRS hSR
  have hp1q1 : ¬ p1 <+: q1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrp hrr) (higmanVCTauConj_mapsCone_symm hrq hrr) hpq
  have hq1p1 : ¬ q1 <+: p1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrq hrr) (higmanVCTauConj_mapsCone_symm hrp hrr) hqp
  have hx1y1 : ¬ x1 <+: y1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrx hrr) (higmanVCTauConj_mapsCone_symm hry hrr) hxy
  have hy1x1 : ¬ y1 <+: x1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hry hrr) (higmanVCTauConj_mapsCone_symm hrx hrr) hyx
  have hx2y2 : ¬ x2 <+: y2 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrx' hrr) (higmanVCTauConj_mapsCone_symm hry' hrr) hxy'
  have hy2x2 : ¬ y2 <+: x2 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hry' hrr) (higmanVCTauConj_mapsCone_symm hrx' hrr) hyx'
  have hconj : coneSwap R S hRS hSR * coneSwap p q hpq hqp * (coneSwap R S hRS hSR)⁻¹ =
      coneSwap p1 q1 hp1q1 hq1p1 :=
    vgen_conj_coneSwap hp1q1 hq1p1 hpq hqp hrp hrq
  have hdx : MapsCone (coneSwap p1 q1 hp1q1 hq1p1) x1 x2 := by
    rw [← hconj, mul_assoc]
    exact (hrx.inv.comp hmx).comp hrx'
  have hdy : MapsCone (coneSwap p1 q1 hp1q1 hq1p1) y1 y2 := by
    rw [← hconj, mul_assoc]
    exact (hry.inv.comp hmy).comp hry'
  have hv : higmanVCTauShort_conjEq d R S p q p1 q1 :=
    higmanVCTauShort_allShort hd hRS hSR hR hS3 ⟨hp, hq, hp1, hq1⟩ hrp hrq hpq hqp hp1q1 hq1p1
  have e1 : higmanVCTauShort_conjEq d R S x y x1 y1 :=
    higmanVCTauDeep_dleg hd hB hS hRS hSR hR hS3 hrx hry hxy hyx hx1y1 hy1x1 hE1
  have e2 : higmanVCTauShort_conjEq d p1 q1 x1 y1 x2 y2 :=
    higmanVCTauDeep_dleg hd hB hS hp1q1 hq1p1 hp1 hq1 hdx hdy hx1y1 hy1x1 hx2y2 hy2x2 hE2
  have e3 : higmanVCTauShort_conjEq d R S x2 y2 x' y' :=
    higmanVCTauDeep_dleg hd hB hS hRS hSR hR hS3 (higmanVCTauConj_mapsCone_symm hrx' hrr)
      (higmanVCTauConj_mapsCone_symm hry' hrr) hx2y2 hy2x2 hxy' hyx' hE3
  unfold higmanVCTauShort_conjEq at hv e1 e2 e3 ⊢
  exact higmanVCTauLevel_groupC (higmanVCTauShort_psi_sq d hR hS3) hv e1 e2 e3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_hopCD_case

end GroupApproximation.BooneHigman.Metabelian.Envelope
