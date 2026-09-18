import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroCubePosEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The reduced char-zero cube gap wired into the six-hypothesis root

Lane `bh-met-90e`, wiring only: it substitutes `czCubePos_charZeroK2CubeGapPos_of_cubePos`
(module `ElemFPCharZeroCubePosEndpoint`) for the hypothesis
`hcube : CharZeroK2CubeGapPosStatement` of `Envelope.hmClosed_finitelyPresentedMetabelian_of_six`.
The new hypothesis `hcp : CZCubePosStatement` is logically equivalent to `hcube` (LOUD) and
strictly smaller in proof content.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- **The six-hypothesis root with `hcube` replaced by `CZCubePosStatement`.** -/
theorem czCubePos_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : CharZeroK2PosStabGenStatement)
    (hcp : CZCubePosStatement)
    (hswap : Envelope.HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  Envelope.hmClosed_finitelyPresentedMetabelian_of_six hH hvdk hloc hgen
    (czCubePos_charZeroK2CubeGapPos_of_cubePos hcp) hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
