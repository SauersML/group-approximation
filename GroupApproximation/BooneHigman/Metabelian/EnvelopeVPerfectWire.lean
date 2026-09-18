import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierThree
import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfect
import GroupApproximation.Meta.AxiomGuard

/-!
# The frontier-three root without the perfectness hypothesis

This module only wires. `genTorsionVPerfect` (module `EnvelopeVPerfect`) proves
`GenTorsionVPerfectStatement` outright, so the hypothesis `hperf` of
`Chain.finitelyPresentedMetabelianStatement_of_frontierThree` is discharged. The root is left with
nine hypotheses.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The frontier-three root with `hperf` discharged** by `genTorsionVPerfect`. -/
theorem vPerfectFinitelyPresentedMetabelian_of_frontierThree
    (hm : Coprimary.PureCharPrimeEHighModuleStatement)
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hbruhat : ElemFP.FieldK2.BruhatBigCellStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement)
    (hrel : RNRelatorsFiniteCoreStatement) : FinitelyPresentedMetabelianStatement :=
  Chain.finitelyPresentedMetabelianStatement_of_frontierThree hm hH hvdk hloc hbruhat hgen hcube
    hswap hrel genTorsionVPerfect

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.vPerfectFinitelyPresentedMetabelian_of_frontierThree

end GroupApproximation.BooneHigman.Metabelian.Envelope
