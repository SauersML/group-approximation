import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondTop
import GroupApproximation.BooneHigman.Products.Assembly
import GroupApproximation.BooneHigman.Products.Hosts
import GroupApproximation.Meta.AxiomGuard

/-!
# Boone–Higman wiring: route A for T1, T2 and T3

This file only composes endpoints of the metabelian chain in `GroupApproximation/BooneHigman/**`.
It adds no new mathematics.  It uses the chain through its named Statements and endpoint theorems,
the same ones `ElemFP.bhNagaoUncond_fpMetabelian_routeA` uses.

Route A has four open inputs, all named Statements of the chain:

* `S1 = Absorption.suslinZLocal_BadStatement` (Suslin absorption, the bad-prime local case);
* `P1 = ∀ p prime, ElemFP.PolyK2NilGapStatementOver (ZMod p) 4` (the char-`p` `K₂` gap pair);
* `Z1 = ElemFPCharZero.CharZeroK2SplitGapStatement` (the char-`0` `K₂` split gap);
* `H1 = Envelope.HigmanVCStepBCoreStatement` (the Higman–`V` step-B core).

From them this file states:

* T1: finitely presented metabelian groups embed in finitely presented simple groups;
* T2: finitely generated metabelian groups embed in finitely presented simple groups;
* T3: finitely generated linear groups over any field embed in finitely presented simple groups.

T1 is `bhNagaoUncond_fpMetabelian_routeA` itself.  T2 and T3 use the linear host and the
self-similar envelope, built from the same inputs by the same reductions as that theorem's body
(`linearHost_routeA`, `envelope_routeA`).  The envelope needs only `H1`.  The linear host needs
`S1`, `P1` and `Z1`.

This module is deliberately not imported by the root.  The Palomar Solution imports it directly.
-/

namespace GroupApproximation
namespace BooneHigmanLinear

open GroupApproximation.BooneHigman

/-- The self-similar envelope from `H1` alone. -/
theorem envelope_routeA (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    Products.FPSelfSimilarEnvelopeStatement := by
  have hA : Metabelian.Envelope.HigmanVCAllAntichainStatement :=
    Metabelian.Envelope.higmanVCStepB_antichain_of_core hH1
  have hV : Metabelian.Envelope.HigmanVFinSectionStatement :=
    Metabelian.Envelope.higmanVFinSection_of_swapSection
      (Metabelian.Envelope.higmanVCTauDone_swapSection_of_antichain hA)
  have hcore : Metabelian.Envelope.RNFreeSectionCoreStatement :=
    Metabelian.Envelope.rnFreeSectionCore_of_normalForm
      (Metabelian.Envelope.higmanVFP_of_complete
        (Metabelian.Envelope.higmanVCTauDone_complete_of_antichain hA))
      (Metabelian.Envelope.rnNormalFormRelators_of_finiteCore Metabelian.Envelope.rnNF_finiteCore)
  exact Metabelian.Chain.fpSelfSimilarEnvelope_of_frontierTwo hV hcore
    Metabelian.Envelope.vPerfect_rnFiniteIndex

#audit_axioms GroupApproximation.BooneHigmanLinear.envelope_routeA

/-- The linear host from `S1`, `Z1` and the char-`p` elementary target: `E_N(F_p[s_1..s_k])` is
finitely presented for `N ≥ k + 4`. -/
theorem linearHost_of_polyFpEFP (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)
    (hfp : Metabelian.ElemFP.PolynomialFpElementaryFPStatement)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement) :
    Products.LinearHostStatement := by
  have habs := Metabelian.Absorption.elementaryAbsorption_of_localGlobalQuillen
    (Metabelian.Absorption.suslinLocalGlobalQuillen_of_localHorrocks
      (Metabelian.Absorption.suslinBase3_localHorrocks Metabelian.Absorption.suslinKill_intCoord
        (Metabelian.Absorption.suslinZLocal_global_of_bad hS1)))
  have hcP : Metabelian.Chain.CharPLinearHostStatement :=
    Metabelian.Chain.charPLinearHostStatement_of_chain
      Metabelian.CharPCoords.charPPolynomialCoordinates habs.1 hfp
      Metabelian.Chain.affineExtensionFPStatement_holds
      Metabelian.CharPHost.TreeHost.charPAffineSelfSimilarStatement_holds
  have hc0 : Metabelian.Chain.CharZeroLinearHostStatement :=
    Metabelian.Chain.charZeroLinearHostStatement_of_chainFive
      Metabelian.CharZeroHost.charZeroPolynomialCoordinates habs.2
      (Metabelian.Chain.charZeroElementaryFPFive_of_stableK2FG
        (Metabelian.ElemFPCharZero.charZeroStableK2FG_of_splitGap hZ1))
      Metabelian.Chain.affineExtensionFPStatement_holds
      Metabelian.CharZeroHost.charZeroAffineSelfSimilarStatement
  exact Metabelian.Chain.linearHostStatement_of_charP_charZero hcP hc0

#audit_axioms GroupApproximation.BooneHigmanLinear.linearHost_of_polyFpEFP

/-- The linear host from `S1`, `P1` and `Z1`. -/
theorem linearHost_routeA (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)
    (hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement) :
    Products.LinearHostStatement :=
  linearHost_of_polyFpEFP hS1
    (Metabelian.ElemFP.polynomialFpElementaryFP_of_polynomialFpK2Vanishing
      (Metabelian.ElemFP.polynomialFpK2Vanishing_of_gapOver hP1
        Metabelian.ElemFP.vdkRowExt_fieldK2Vanishing))
    hZ1

#audit_axioms GroupApproximation.BooneHigmanLinear.linearHost_routeA

/-- The coprimary splitting, with no open input (its high-exponent module input is proved). -/
theorem coprimarySplitting_routeA : Metabelian.Coprimary.CoprimarySplittingStatement :=
  Metabelian.Coprimary.coprimarySplitting_of_linearity
    (Metabelian.Coprimary.pureCharLinearity_of_split
      (Metabelian.Coprimary.pureCharPrimeSplit_of_eOne_high Metabelian.Coprimary.pureCharPrimeEOne
        (Metabelian.Coprimary.pureCharPrimeEHigh_of_module
          Metabelian.Coprimary.eHighWittE_pureCharPrimeEHighModule)))

#audit_axioms GroupApproximation.BooneHigmanLinear.coprimarySplitting_routeA

/-- **T1 (route A).**  Finitely presented metabelian groups embed in finitely presented simple
groups, given `S1`, `P1`, `Z1` and `H1`. -/
theorem finitelyPresentedMetabelianStatement_routeA
    (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)
    (hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    FinitelyPresentedMetabelianStatement :=
  Metabelian.ElemFP.bhNagaoUncond_fpMetabelian_routeA hS1 hP1 hZ1 hH1

#audit_axioms GroupApproximation.BooneHigmanLinear.finitelyPresentedMetabelianStatement_routeA

/-- **T2 (route A).**  Finitely generated metabelian groups embed in finitely presented simple
groups, given `S1`, `P1`, `Z1` and `H1`. -/
theorem finitelyGeneratedMetabelianStatement_routeA
    (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)
    (hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    FinitelyGeneratedMetabelianStatement :=
  Products.finitelyGeneratedMetabelianStatement_of_pieces
    (Metabelian.Coprimary.metabelianPieces_of_splitting coprimarySplitting_routeA
      (linearHost_routeA hS1 hP1 hZ1))
    (envelope_routeA hH1)

#audit_axioms GroupApproximation.BooneHigmanLinear.finitelyGeneratedMetabelianStatement_routeA

/-- **T3 (route A).**  Every finitely generated subgroup of `GL_n(K)`, for any field `K`, embeds in
a finitely presented simple group, given `S1`, `P1`, `Z1` and `H1`. -/
theorem finitelyGeneratedLinearStatement_routeA
    (hS1 : Metabelian.Absorption.suslinZLocal_BadStatement)
    (hP1 : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hZ1 : Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Metabelian.Envelope.HigmanVCStepBCoreStatement) :
    FinitelyGeneratedLinearStatement :=
  Products.finitelyGeneratedLinearStatement_of_hosts (linearHost_routeA hS1 hP1 hZ1)
    (envelope_routeA hH1)

#audit_axioms GroupApproximation.BooneHigmanLinear.finitelyGeneratedLinearStatement_routeA

end BooneHigmanLinear
end GroupApproximation
