import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfectWire
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormFinal
import GroupApproximation.Meta.AxiomGuard

/-!
# The RN relator gap, discharged

Lane bh-met-57e proves `RNRelatorsFiniteCoreStatement` outright (`rnNF_finiteCore`). This file
drops the `hrel` hypothesis from the frontier-three root with `hperf` already discharged.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The frontier-three root with `hperf` and `hrel` discharged.** -/
theorem rnNFWire_finitelyPresentedMetabelian
    (hm : Coprimary.PureCharPrimeEHighModuleStatement)
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hbruhat : ElemFP.FieldK2.BruhatBigCellStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  vPerfectFinitelyPresentedMetabelian_of_frontierThree hm hH hvdk hloc hbruhat hgen hcube
    hswap rnNF_finiteCore

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.rnNFWire_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
