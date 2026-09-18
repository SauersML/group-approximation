import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormWire
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The high-exponent module gap, discharged

Lane bh-met-87h proves `PureCharPrimeEHighModuleStatement` outright
(`Coprimary.eHighWittE_pureCharPrimeEHighModule`, through the infinite mixed case for every
`e ≥ 2`). This file drops the `hm` hypothesis from `rnNFWire_finitelyPresentedMetabelian`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The frontier-three root with `hperf`, `hrel` and `hm` discharged.** -/
theorem hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hbruhat : ElemFP.FieldK2.BruhatBigCellStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  rnNFWire_finitelyPresentedMetabelian Coprimary.eHighWittE_pureCharPrimeEHighModule hH hvdk
    hloc hbruhat hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
