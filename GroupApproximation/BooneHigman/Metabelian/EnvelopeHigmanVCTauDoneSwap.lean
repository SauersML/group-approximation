import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDoneTau
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVPresentReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYWire
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCLeafExpReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGapReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenWire
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonCentral
import GroupApproximation.Meta.AxiomGuard

/-!
# `hswap` from the antichain half alone (lane bh-met-93b)

This is pure wiring.  Every existing theorem that proves `HigmanVSwapSectionStatement` (or
`HigmanVFinFPStatement`) from a Statement *and* the τ half `hB` gets its `hB` filled in with
`higmanVCTauDone_tau`, so only the other Statement is left.

The weakest of these Statements is `HigmanVCAllAntichainStatement`.  It is equivalent to
half (1) of the transfer, `ker (higmanVC_evalAll d) ≤ normalClosure (higmanVC_rels d ⊤)`
(`higmanVCAll_ker_le_of_antichain`, `higmanVCAll_antichain_of_ker_le`).  Every other
Statement used here implies it: Z, Y, W, Orbit, Gap, All, Gen and CommonCentral.

No new Statements are introduced.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Finite presentability of `V_d` from the antichain half alone. -/
theorem higmanVCTauDone_finFP_of_antichain (hA : HigmanVCAllAntichainStatement) :
    HigmanVFinFPStatement :=
  higmanVCAll_finFP_of_antichain_of_tau hA higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_finFP_of_antichain

/-- Short completeness from the antichain half alone. -/
theorem higmanVCTauDone_complete_of_antichain (hA : HigmanVCAllAntichainStatement) :
    HigmanVFPShortCompleteStatement :=
  higmanVCAll_complete_of_antichain_of_tau hA higmanVCTauDone_tau

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_complete_of_antichain

/-- **`hswap` from the antichain half alone.** -/
theorem higmanVCTauDone_swapSection_of_antichain (hA : HigmanVCAllAntichainStatement) :
    HigmanVSwapSectionStatement :=
  higmanVPresent_swapSection_of_finFP (higmanVCTauDone_finFP_of_antichain hA)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_antichain

/-- **`hswap` from half (1) of the transfer, stated literally.** -/
theorem higmanVCTauDone_swapSection_of_ker_le
    (h : ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) :
    HigmanVSwapSectionStatement :=
  higmanVCTauDone_swapSection_of_antichain (higmanVCAll_antichain_of_ker_le h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_ker_le

/-- `hswap` from Z alone. -/
theorem higmanVCTauDone_swapSection_of_Z (hZ : HigmanVCPivotYStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCPivotY_swapSection_of_Z_of_tau hZ higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_Z

/-- `hswap` from Y alone. -/
theorem higmanVCTauDone_swapSection_of_Y (hY : HigmanVCPivotACStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCPivotY_swapSection_of_Y_of_tau hY higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_Y

/-- `hswap` from W alone. -/
theorem higmanVCTauDone_swapSection_of_W (hW : HigmanVCLeafExpStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCLeafExp_swapSection_of_W_of_tau hW higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_W

/-- `hswap` from the orbit statement alone. -/
theorem higmanVCTauDone_swapSection_of_orbit (hO : HigmanVCOrbitStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbit_swapSection_of_orbit_of_tau hO higmanVCTauDone_tau

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_orbit

/-- `hswap` from the orbit-gap statement alone. -/
theorem higmanVCTauDone_swapSection_of_gap (hG : HigmanVCOrbitGapStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbitGap_swapSection_of_tau hG higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_gap

/-- `hswap` from the orbit-gen statement alone. -/
theorem higmanVCTauDone_swapSection_of_gen (hG : HigmanVCOrbitGenStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbitGen_swapSection_of_tau hG higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_gen

/-- `hswap` from the orbit-all statement alone. -/
theorem higmanVCTauDone_swapSection_of_orbitAll (hA : HigmanVCOrbitAllStatement) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbitAll_swapSection_of_tau hA higmanVCTauDone_tau

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_orbitAll

/-- `hswap` from the common-central statement alone. -/
theorem higmanVCTauDone_swapSection_of_central (hA : HigmanVCCommonCentralStatement) :
    HigmanVSwapSectionStatement :=
  higmanVPresent_swapSection_of_finFP (higmanVCCommon_finFP_of_central hA higmanVCTauDone_tau)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_swapSection_of_central

end GroupApproximation.BooneHigman.Metabelian.Envelope
