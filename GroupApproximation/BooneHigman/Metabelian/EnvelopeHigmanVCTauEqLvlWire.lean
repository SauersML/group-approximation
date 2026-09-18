import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Residual
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The equal-level residual feeds `τ` and the BH root (lane bh-met-77z)

`higmanVCTauD2_residual` (lane 77v) discharges the lower-level bridge residual.  What is left
of the `τ` input `hB` is therefore only the equal-level statement
`HigmanVCTauTightEqStatement`.

* `higmanVCTauEqLvl_tau_of_eq`: TightEq gives `HigmanVCTauStatement`, which is `hB`.
* `higmanVCTauEqLvl_swapSection_of_orbit_of_eq`: the orbit residual and TightEq give `hswap`.
* `higmanVCTauEqLvl_finitelyPresentedMetabelian`: `higmanVCPivotY_finitelyPresentedMetabelian`
  with `hZ` replaced by the orbit residual and `hB` replaced by TightEq.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **`τ` from the equal-level residual.**  The lower-level residual: `higmanVCTauD2_residual`. -/
theorem higmanVCTauEqLvl_tau_of_eq (h : HigmanVCTauTightEqStatement) : HigmanVCTauStatement :=
  higmanVCTauTightEq_tau_of_eq_of_residual h higmanVCTauD2_residual

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_tau_of_eq

/-- **`hswap`** from the orbit residual and the equal-level residual. -/
theorem higmanVCTauEqLvl_swapSection_of_orbit_of_eq (hO : HigmanVCOrbitStatement)
    (h : HigmanVCTauTightEqStatement) : HigmanVSwapSectionStatement :=
  higmanVCOrbit_swapSection_of_orbit_of_tau hO (higmanVCTauEqLvl_tau_of_eq h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_swapSection_of_orbit_of_eq

/-- **BH root.**  This is the current best root (`higmanVCPivotY_finitelyPresentedMetabelian`)
with `hZ` taken from the orbit residual (`higmanVCOrbit_Z_of_orbit`) and `hB` taken from the
equal-level residual. -/
theorem higmanVCTauEqLvl_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hO : HigmanVCOrbitStatement)
    (h : HigmanVCTauTightEqStatement) :
    FinitelyPresentedMetabelianStatement :=
  higmanVCPivotY_finitelyPresentedMetabelian hH hvdk hloc hgen hcube
    (higmanVCOrbit_Z_of_orbit hO) (higmanVCTauEqLvl_tau_of_eq h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_finitelyPresentedMetabelian

/-- **BH root, pivot form.**  The same root, keeping `hZ = HigmanVCPivotYStatement`. -/
theorem higmanVCTauEqLvl_fpMetabelian_of_Z
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hZ : HigmanVCPivotYStatement)
    (h : HigmanVCTauTightEqStatement) :
    FinitelyPresentedMetabelianStatement :=
  higmanVCPivotY_finitelyPresentedMetabelian hH hvdk hloc hgen hcube hZ
    (higmanVCTauEqLvl_tau_of_eq h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_fpMetabelian_of_Z

end GroupApproximation.BooneHigman.Metabelian.Envelope
