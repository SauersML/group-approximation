import GroupApproximation.BooneHigman.Metabelian.SuslinKillStep
import GroupApproximation.BooneHigman.Metabelian.SuslinR1PrimeMonic
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicConstLead
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 7: the endpoints

Lane `bh-met-91t`.  `ℤ[1/m]` (`m ≠ 0`) is a PID domain, so `suslinKill_M_all` proves
`suslinR1Prime_MonicStatement` outright (no Suslin/Quillen/Horrocks input).  Hence
`suslinMonic_ConstLeadStatement` (via `suslinMonic_constLead_of_monic`),
`SuslinR1FinIntCoordStatement` (via `suslinR1Prime_intCoord_of_monic`), and the frontier root
`Envelope.suslinMonic_finitelyPresentedMetabelian` with its `hcl` argument discharged.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **`suslinR1Prime_MonicStatement`, proved.** -/
theorem suslinKill_monicStatement : suslinR1Prime_MonicStatement := by
  intro m k hm J hJ
  haveI : IsDomain (Localization.Away (m : ℤ)) := CharZeroHost.isDomain_away hm
  haveI : IsPrincipalIdealRing (Localization.Away (m : ℤ)) := suslinKill_away_pid m
  exact suslinKill_M_all (Localization.Away (m : ℤ)) k J hJ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_monicStatement

/-- **The lane target `suslinMonic_ConstLeadStatement`, proved.** -/
theorem suslinKill_constLeadStatement : suslinMonic_ConstLeadStatement :=
  suslinMonic_constLead_of_monic suslinKill_monicStatement

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_constLeadStatement

/-- `SuslinR1FinIntCoordStatement`, proved. -/
theorem suslinKill_intCoord : SuslinR1FinIntCoordStatement :=
  suslinR1Prime_intCoord_of_monic suslinKill_monicStatement

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_intCoord

end Absorption

namespace Envelope

/-- The frontier root with the Suslin coordinate input discharged. -/
theorem suslinKill_finitelyPresentedMetabelian
    (h : Absorption.SuslinBase3CoreGlobalStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  suslinMonic_finitelyPresentedMetabelian Absorption.suslinKill_constLeadStatement h hvdk
    hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.suslinKill_finitelyPresentedMetabelian

end Envelope
end Metabelian
end BooneHigman
end GroupApproximation
