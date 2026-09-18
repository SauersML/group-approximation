import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlFinal
import GroupApproximation.Meta.AxiomGuard

/-!
# The equal-level residual reduces to `d = 2` letters (lane bh-met-77z)

* `higmanVCTauEqLvl_tightEq_of_d2`: `higmanVCTauEqLvl_D2Residual` gives
  `HigmanVCTauTightEqStatement`, because every `d ≥ 3` instance is vacuous
  (`higmanVCTauEqLvl_three`).
* `higmanVCTauEqLvl_tightEq_iff_d2`: the two are **EQUIVALENT** (loud).  The `d = 2` residual is
  smaller in proof content only.
* `higmanVCTauEqLvl_tau_of_d2`, `higmanVCTauEqLvl_fpMetabelian_of_d2`: the `τ` input and the
  BH root, taken from the `d = 2` residual.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **TightEq from its `d = 2` case.** -/
theorem higmanVCTauEqLvl_tightEq_of_d2 (h : higmanVCTauEqLvl_D2Residual) :
    HigmanVCTauTightEqStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hx hx' hSh hs hOA hOE hOR hFA hFB hFA' hFB'
    hmx hmy hxy hyx hxy' hyx'
  by_cases hd2 : d = 2
  · exact h d hd2 n hB p q x y x' y' hpq hqp hp hq hx hx' hSh hs hOA hOE hOR hFA hFB hFA'
      hFB' hmx hmy hxy hyx hxy' hyx'
  · exfalso
    rcases higmanVCTauEqLvl_three (by omega) hpq hqp hp hq (by omega) hs hmx hmy hxy hyx
      hxy' hyx' with h1 | h1 | h1 | h1
    · exact hFA h1
    · exact hFB h1
    · exact hFA' h1
    · exact hFB' h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_tightEq_of_d2

/-- The `d = 2` residual is a special case of TightEq. -/
theorem higmanVCTauEqLvl_d2_of_tightEq (h : HigmanVCTauTightEqStatement) :
    higmanVCTauEqLvl_D2Residual :=
  fun d hd2 => h d (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_d2_of_tightEq

/-- **Loud: EQUIVALENT**, not strictly weaker. -/
theorem higmanVCTauEqLvl_tightEq_iff_d2 :
    HigmanVCTauTightEqStatement ↔ higmanVCTauEqLvl_D2Residual :=
  ⟨higmanVCTauEqLvl_d2_of_tightEq, higmanVCTauEqLvl_tightEq_of_d2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_tightEq_iff_d2

/-- **`τ` from the `d = 2` residual.** -/
theorem higmanVCTauEqLvl_tau_of_d2 (h : higmanVCTauEqLvl_D2Residual) : HigmanVCTauStatement :=
  higmanVCTauEqLvl_tau_of_eq (higmanVCTauEqLvl_tightEq_of_d2 h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_tau_of_d2

/-- **BH root** with `hB` taken from the `d = 2` equal-level residual. -/
theorem higmanVCTauEqLvl_fpMetabelian_of_d2
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hO : HigmanVCOrbitStatement)
    (h : higmanVCTauEqLvl_D2Residual) :
    FinitelyPresentedMetabelianStatement :=
  higmanVCTauEqLvl_finitelyPresentedMetabelian hH hvdk hloc hgen hcube hO
    (higmanVCTauEqLvl_tightEq_of_d2 h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_fpMetabelian_of_d2

end GroupApproximation.BooneHigman.Metabelian.Envelope
