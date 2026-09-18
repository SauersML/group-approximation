import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierThree
import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwo
import GroupApproximation.BooneHigman.Products.Hosts
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEWire
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellEndpoint
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormFinal
import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfect
import GroupApproximation.Meta.AxiomGuard

/-!
# Boone–Higman wiring, frontier four

This file only composes existing endpoints of the metabelian chain in
`GroupApproximation/BooneHigman/**`; it adds no new mathematics and uses that chain only
through its named Statements and endpoint theorems.

Of the ten gap Statements of `Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierThree`,
four are now proved outright on main and are plugged in here:

* item 1, `Coprimary.eHighWittE_pureCharPrimeEHighModule`;
* item 5, `ElemFP.FieldK2.bruhatBigCell`;
* item 9, `Envelope.rnNF_finiteCore`;
* item 10, `Envelope.genTorsionVPerfect`.

The two theorems below therefore state

* T1, finitely presented metabelian groups embed in finitely presented simple groups, and
* T3, finitely generated linear groups over any field embed in finitely presented simple groups,

from exactly the six remaining gap Statements (items 2, 3, 4, 6, 7, 8):

* `hH : Absorption.SuslinLocalHorrocksStatement` (item 2),
* `hvdk : ElemFP.VdKRowExtensionStatement` (item 3),
* `hloc : ElemFP.PolyK2CubeNilLocalStatement` (item 4),
* `hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement` (item 6),
* `hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement` (item 7),
* `hswap : Envelope.HigmanVSwapSectionStatement` (item 8).

T3 goes through `Products.finitelyGeneratedLinearStatement_of_hosts`, with the linear host from
`Chain.linearHostStatement_of_frontierTwo` and the self-similar envelope from
`Chain.fpSelfSimilarEnvelope_of_frontierTwo`, using the same reductions as the frontier-three
file.  This module is deliberately not imported by the root; the Palomar Solution imports it
directly.
-/

namespace GroupApproximation
namespace BooneHigmanLinear

/-- **T1 from the six open gaps**: finitely presented metabelian groups embed in finitely
presented simple groups, given gap Statements 2, 3, 4, 6, 7 and 8 of the metabelian chain (the
other four are proved and supplied here). -/
theorem finitelyPresentedMetabelianStatement_of_frontierFour
    (hH : GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalHorrocksStatement)
    (hvdk : GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowExtensionStatement)
    (hloc : GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube :
      GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVSwapSectionStatement) :
    GroupApproximation.BooneHigman.FinitelyPresentedMetabelianStatement :=
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierThree
    GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pureCharPrimeEHighModule
    hH hvdk hloc
    GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell
    hgen hcube hswap
    GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_finiteCore
    GroupApproximation.BooneHigman.Metabelian.Envelope.genTorsionVPerfect

#audit_axioms
  GroupApproximation.BooneHigmanLinear.finitelyPresentedMetabelianStatement_of_frontierFour

/-- **T3 from the six open gaps**: every finitely generated subgroup of `GL_n(K)`, for any field
`K`, embeds in a finitely presented simple group, given gap Statements 2, 3, 4, 6, 7 and 8 of the
metabelian chain (T3 does not use item 1; items 5, 9 and 10 are proved and supplied here). -/
theorem finitelyGeneratedLinearStatement_of_frontierFour
    (hH : GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalHorrocksStatement)
    (hvdk : GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowExtensionStatement)
    (hloc : GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube :
      GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVSwapSectionStatement) :
    GroupApproximation.BooneHigman.FinitelyGeneratedLinearStatement :=
  GroupApproximation.BooneHigman.Products.finitelyGeneratedLinearStatement_of_hosts
    (GroupApproximation.BooneHigman.Metabelian.Chain.linearHostStatement_of_frontierTwo
      (GroupApproximation.BooneHigman.Metabelian.Absorption.polynomialSuslin_of_oneVariable
        (GroupApproximation.BooneHigman.Metabelian.Absorption.suslinOneVariable_of_patching
          (GroupApproximation.BooneHigman.Metabelian.Absorption.suslinPatching_of_localHorrocks
            hH)))
      (GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2StabRangeDiag_of_vdkRowExtension hvdk)
      (GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_cubeLocal hloc)
      (GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.fieldK2Vanishing_of_bruhatBigCell
        GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell)
      (GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroStableK2FG_of_basePos_of_cubeGapPos
        (GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2BasePos_of_stabGen hgen)
        hcube))
    (GroupApproximation.BooneHigman.Metabelian.Chain.fpSelfSimilarEnvelope_of_frontierTwo
      (GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFinSection_of_swapSection hswap)
      (GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeSectionCore_of_normalForm
        (GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_of_finSection
          (GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFinSection_of_swapSection
            hswap))
        (GroupApproximation.BooneHigman.Metabelian.Envelope.rnNormalFormRelators_of_finiteCore
          GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_finiteCore))
      (GroupApproximation.BooneHigman.Metabelian.Envelope.rnFiniteIndex_of_vPerfect
        GroupApproximation.BooneHigman.Metabelian.Envelope.genTorsionVPerfect))

#audit_axioms
  GroupApproximation.BooneHigmanLinear.finitelyGeneratedLinearStatement_of_frontierFour

end BooneHigmanLinear
end GroupApproximation
