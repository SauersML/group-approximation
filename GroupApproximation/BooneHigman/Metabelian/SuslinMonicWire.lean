import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CoreEndpoint
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicConstLead
import GroupApproximation.Meta.AxiomGuard

/-!
# Wiring the Nagata step into the Suslin half of the root

Lane `bh-met-91n`.  `Envelope.suslinBase3Core_finitelyPresentedMetabelian` with its argument
`hc : SuslinR1FinIntCoordStatement` replaced by the residual `suslinMonic_ConstLeadStatement`
(`suslinMonic_intCoord_of_constLead`: Nagata step, prime avoidance, transport and the
primewise criterion are proved).  The other hypotheses are unchanged.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Local Horrocks from the residual and the congruence core. -/
theorem suslinMonic_localHorrocks (hcl : suslinMonic_ConstLeadStatement)
    (h : SuslinBase3CoreGlobalStatement) : SuslinLocalHorrocksStatement :=
  suslinBase3Core_localHorrocks (suslinMonic_intCoord_of_constLead hcl) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_localHorrocks

end Absorption

namespace Envelope

/-- **The frontier root with `hc` replaced** by the residual `suslinMonic_ConstLeadStatement`. -/
theorem suslinMonic_finitelyPresentedMetabelian
    (hcl : Absorption.suslinMonic_ConstLeadStatement)
    (h : Absorption.SuslinBase3CoreGlobalStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  suslinBase3Core_finitelyPresentedMetabelian
    (Absorption.suslinMonic_intCoord_of_constLead hcl) h hvdk hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinMonic_finitelyPresentedMetabelian

end Envelope
end Metabelian
end BooneHigman
end GroupApproximation
