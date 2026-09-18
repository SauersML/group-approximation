import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormWire
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEWire
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The high-exponent module and Bruhat gaps, discharged

Lane bh-met-87h proves `PureCharPrimeEHighModuleStatement` outright
(`Coprimary.eHighWittE_pureCharPrimeEHighModule`, through the infinite mixed case for every
`e ≥ 2`). Lane bh-met-64c proves `BruhatBigCellStatement` outright
(`ElemFP.FieldK2.bruhatBigCell`). This file drops `hm` and `hbruhat` from
`rnNFWire_finitelyPresentedMetabelian`.
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

/-- **The frontier-three root with `hperf`, `hrel`, `hm` and `hbruhat` discharged.** -/
theorem hmClosed_finitelyPresentedMetabelian_of_six
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian hH hvdk hloc ElemFP.FieldK2.bruhatBigCell hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.hmClosed_finitelyPresentedMetabelian_of_six

end GroupApproximation.BooneHigman.Metabelian.Envelope
