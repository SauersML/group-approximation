import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroRankFourFPReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.BooneHigman.Metabelian.ElemFPVdKHighWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Boone–Higman roots with `hgen` replaced by `SL_4(ℤ[1/m])` f.p. (lane bh-met-91a, wiring)

`ElemFPCharZero.czRankFourFP_posStabGen_of_sl` derives `hgen`
(`ElemFPCharZero.CharZeroK2PosStabGenStatement`) from the residual
`ElemFPCharZero.czRankFourFP_SLFourStatement` (`SL_4(ℤ[1/m])` finitely presented, `m ≥ 1`).
This file substitutes it into two roots:

* `Envelope.czRankFourFP_hmClosed_fpMetabelian_of_six`
  (from `Envelope.hmClosed_finitelyPresentedMetabelian_of_six`);
* `Envelope.czRankFourFP_vdkHigh_fpMetabelian_of_six`
  (from `Envelope.vdkHighWire_finitelyPresentedMetabelian_of_six`).

**LOUD (strength).**  Given the closed TriOff lane, `hgen` is equivalent to "`E_5(ℤ[1/m])` is
finitely presented for `m ≥ 1`": the rank-five Steinberg group is finitely presented in the
corpus, so `hgen ↔ (K₂(5, ℤ[1/m])` finitely normally generated`)`.  The residual used here is a
rank-**four** statement and implies `hgen`; the converse is not proved.  So these roots trade
`hgen` for a hypothesis that is K₂-free and Steinberg-free, but not logically weaker than
`hgen`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `hmClosed_finitelyPresentedMetabelian_of_six` with `hgen` replaced by the residual
`SL_4(ℤ[1/m])` f.p. -/
theorem czRankFourFP_hmClosed_fpMetabelian_of_six
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hsl : ElemFPCharZero.czRankFourFP_SLFourStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH hvdk hloc
    (ElemFPCharZero.czRankFourFP_posStabGen_of_sl hsl) hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.czRankFourFP_hmClosed_fpMetabelian_of_six

/-- `vdkHighWire_finitelyPresentedMetabelian_of_six` with `hgen` replaced by the residual
`SL_4(ℤ[1/m])` f.p. -/
theorem czRankFourFP_vdkHigh_fpMetabelian_of_six
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hdiag : ElemFP.vdkInj_DiagStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hsl : ElemFPCharZero.czRankFourFP_SLFourStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  vdkHighWire_finitelyPresentedMetabelian_of_six hH hdiag hloc
    (ElemFPCharZero.czRankFourFP_posStabGen_of_sl hsl) hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.czRankFourFP_vdkHigh_fpMetabelian_of_six

end GroupApproximation.BooneHigman.Metabelian.Envelope
