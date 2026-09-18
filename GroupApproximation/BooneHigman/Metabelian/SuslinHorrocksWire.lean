import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks, part 5: the root wire

Lane `bh-met-90a`.  The gap `hH : Absorption.SuslinLocalHorrocksStatement` of
`Envelope.hmClosed_finitelyPresentedMetabelian_of_six` is replaced by the split Statement
`Absorption.SuslinHorrocksSplitStatement` (`SuslinHorrocksStatement.lean`).  That Statement is
EQUIVALENT to `SuslinLocalCaseFamilyStatement`, but with the local Horrocks step proved outright
(`Absorption.suslinHorrocks_row`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Root wire**: `FinitelyPresentedMetabelianStatement` from the split Horrocks Statement and
the other five gaps of `hmClosed_finitelyPresentedMetabelian_of_six`. -/
theorem suslinHorrocks_finitelyPresentedMetabelian_of_split
    (hS : Absorption.SuslinHorrocksSplitStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six (Absorption.suslinHorrocks_localHorrocks_of_split hS)
    hvdk hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinHorrocks_finitelyPresentedMetabelian_of_split

end GroupApproximation.BooneHigman.Metabelian.Envelope
