import GroupApproximation.BooneHigman.Products.Assembly
import GroupApproximation.BooneHigman.Metabelian.CoprimaryStatement
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeClosed
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeESplit
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProof
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighReduce
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEWire
import GroupApproximation.BooneHigman.Metabelian.ChainQuasiLinear
import GroupApproximation.BooneHigman.Metabelian.ChainCharP
import GroupApproximation.BooneHigman.Metabelian.ChainFiveCharZero
import GroupApproximation.BooneHigman.Metabelian.ChainFiveStableK2
import GroupApproximation.BooneHigman.Metabelian.ChainWiredAffine
import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwo
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalPatching
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalHorrocksStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Endpoint
import GroupApproximation.BooneHigman.Metabelian.SuslinZLocalEndpoint
import GroupApproximation.BooneHigman.Metabelian.SuslinKillEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilCharP
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBCore
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDoneSwap
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPBall
import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsFiniteStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormFinal
import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfect
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeClosed
import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost
import GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsAssembly
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Endpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondChain
import GroupApproximation.Meta.AxiomGuard

/-!
# The Boone–Higman metabelian target, with the Nagao inputs discharged

Lane `bh-wire-01`, part 3 of 3 (a wiring lane: no new residual).  This traces route A of the
metabelian frontier to `FinitelyPresentedMetabelianStatement`.  Every node is a proved theorem
except these four open statements:

* `S1 = Absorption.suslinZLocal_BadStatement` (Suslin absorption, the bad-prime local case);
* `P1 = ∀ p prime, PolyK2NilGapStatementOver (ZMod p) 4` (the char-`p` `K₂` gap pair);
* `Z1 = ElemFPCharZero.CharZeroK2SplitGapStatement` (the char-`0` `K₂` split gap);
* `H1 = Envelope.HigmanVCStepBCoreStatement` (the Higman–`V` step-B core).

LOUD: the Nagao work (`k2PolyNagaoJRes_statement`, `k2PolyNagaoTorus_torusIface`) removes NONE
of `S1, P1, Z1, H1`.  It proves `K₂(N, F_p[X]) = ⊥` (`N ≥ 5`), i.e. the `k ≤ 1` slice of the
`F_p` vanishing (`bhNagaoUncond_polynomialFpK2Vanishing_le_one`).  Inside `P1` this is only the
`k = 1` base instance of the StabRangeDiag conjunct.  The OneVarNil conjunct is not shrunk,
because its `k = 0` instance already follows from its `k = 1` instance
(`ElemFPBhNagaoWireZeroOne`).  The `k ≥ 2` instances of StabRangeDiag stay open.

* `bhNagaoUncond_fpMetabelian_of_polyFpEFP`: the top target from
  `S1`, `Z1`, `H1` and the char-`p` target `PolynomialFpElementaryFPStatement`.
* `bhNagaoUncond_fpMetabelian_routeA`: the top target from `S1`, `P1`, `Z1`,
  `H1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **Route A with the char-`p` elementary target as input**: `S1`, `Z1`, `H1` and
`PolynomialFpElementaryFPStatement` give `FinitelyPresentedMetabelianStatement`. -/
theorem bhNagaoUncond_fpMetabelian_of_polyFpEFP
    (hS1 : Absorption.suslinZLocal_BadStatement) (hfp : PolynomialFpElementaryFPStatement)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyPresentedMetabelianStatement := by
  have hA : Envelope.HigmanVCAllAntichainStatement := Envelope.higmanVCStepB_antichain_of_core hH1
  have hV : Envelope.HigmanVFinSectionStatement := Envelope.higmanVFinSection_of_swapSection
    (Envelope.higmanVCTauDone_swapSection_of_antichain hA)
  have hcore : Envelope.RNFreeSectionCoreStatement := Envelope.rnFreeSectionCore_of_normalForm
    (Envelope.higmanVFP_of_complete (Envelope.higmanVCTauDone_complete_of_antichain hA))
    (Envelope.rnNormalFormRelators_of_finiteCore Envelope.rnNF_finiteCore)
  have henv : Products.FPSelfSimilarEnvelopeStatement :=
    Chain.fpSelfSimilarEnvelope_of_frontierTwo hV hcore Envelope.vPerfect_rnFiniteIndex
  have habs := Absorption.elementaryAbsorption_of_localGlobalQuillen
    (Absorption.suslinLocalGlobalQuillen_of_localHorrocks
      (Absorption.suslinBase3_localHorrocks Absorption.suslinKill_intCoord
        (Absorption.suslinZLocal_global_of_bad hS1)))
  have hcP : Chain.CharPLinearHostStatement :=
    Chain.charPLinearHostStatement_of_chain CharPCoords.charPPolynomialCoordinates habs.1 hfp
      Chain.affineExtensionFPStatement_holds
      CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds
  have hc0 : Chain.CharZeroLinearHostStatement :=
    Chain.charZeroLinearHostStatement_of_chainFive CharZeroHost.charZeroPolynomialCoordinates
      habs.2
      (Chain.charZeroElementaryFPFive_of_stableK2FG
        (ElemFPCharZero.charZeroStableK2FG_of_splitGap hZ1))
      Chain.affineExtensionFPStatement_holds CharZeroHost.charZeroAffineSelfSimilarStatement
  have hsplit : Coprimary.CoprimarySplittingStatement :=
    Coprimary.coprimarySplitting_of_linearity
      (Coprimary.pureCharLinearity_of_split
        (Coprimary.pureCharPrimeSplit_of_eOne_high Coprimary.pureCharPrimeEOne
          (Coprimary.pureCharPrimeEHigh_of_module
            Coprimary.eHighWittE_pureCharPrimeEHighModule)))
  exact Products.finitelyPresentedMetabelianStatement_of_pieces
    (Coprimary.metabelianPieces_of_splitting hsplit
      (Chain.linearHostStatement_of_charP_charZero hcP hc0)) henv

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_fpMetabelian_of_polyFpEFP

/-- **The updated conditional top-level result (route A)**: `FinitelyPresentedMetabelianStatement`
from exactly the four open statements `S1`, `P1`, `Z1`, `H1`.  The field case of `P1`'s endpoint
is `vdkRowExt_fieldK2Vanishing` (proved). -/
theorem bhNagaoUncond_fpMetabelian_routeA
    (hS1 : Absorption.suslinZLocal_BadStatement)
    (hP1 : ∀ p : ℕ, p.Prime → PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyPresentedMetabelianStatement :=
  bhNagaoUncond_fpMetabelian_of_polyFpEFP hS1
    (polynomialFpElementaryFP_of_polynomialFpK2Vanishing
      (polynomialFpK2Vanishing_of_gapOver hP1 vdkRowExt_fieldK2Vanishing))
    hZ1 hH1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoUncond_fpMetabelian_routeA

end GroupApproximation.BooneHigman.Metabelian.ElemFP
