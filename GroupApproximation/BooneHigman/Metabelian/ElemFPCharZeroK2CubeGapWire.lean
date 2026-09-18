import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierThree
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeGapLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# The local cube gap over `ℤ[1/m]` wired into the frontier-three root

Lane `bh-met-73c`.  This module only wires: it substitutes
`charZeroK2CubeGapPos_of_czCubeGapLocal` (module `ElemFPCharZeroK2CubeGapLocal`) for the
hypothesis `hcube : CharZeroK2CubeGapPosStatement` of
`Chain.finitelyPresentedMetabelianStatement_of_frontierThree`.  The new hypothesis
`hcz : CZCubeGapLocalStatement` is logically equivalent to `hcube` and strictly smaller in proof
content (see `ElemFPCharZeroK2CubeGapLocal`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- **The root with the char-zero cube gap in local form**: the frontier-three root, with
`hcube` replaced by `CZCubeGapLocalStatement`. -/
theorem czCubeGapFinitelyPresentedMetabelian_of_frontierThree
    (hm : Coprimary.PureCharPrimeEHighModuleStatement)
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hbruhat : ElemFP.FieldK2.BruhatBigCellStatement)
    (hgen : CharZeroK2PosStabGenStatement)
    (hcz : CZCubeGapLocalStatement)
    (hswap : Envelope.HigmanVSwapSectionStatement)
    (hrel : Envelope.RNRelatorsFiniteCoreStatement)
    (hperf : Envelope.GenTorsionVPerfectStatement) : FinitelyPresentedMetabelianStatement :=
  Chain.finitelyPresentedMetabelianStatement_of_frontierThree hm hH hvdk hloc hbruhat hgen
    (charZeroK2CubeGapPos_of_czCubeGapLocal hcz) hswap hrel hperf

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeGapFinitelyPresentedMetabelian_of_frontierThree

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
