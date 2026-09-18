import GroupApproximation.BooneHigman.Metabelian.TorsionFreeClosedChain
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneProof
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeESplit
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighReduce
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalHorrocksStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatching
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilLocal
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2PosStabGen
import GroupApproximation.BooneHigman.Metabelian.ElemFPZInvK2Endpoint
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsFiniteStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsion
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring, frontier three (lane bh-met-69)

This file only wires existing endpoints; it adds no new mathematics.  It starts from
`finitelyPresentedMetabelianStatement_of_frontierTwo_zeroClosed` (`TorsionFreeClosedChain`),
which takes 9 gap Statements.  Each one is replaced by the smallest current gap on disk.

**The remaining frontier (10 Statements).**  For each: the new gap, the old hypothesis it
replaces, the reduction used, and how their strengths compare.

1. `Coprimary.PureCharPrimeEHighModuleStatement` replaces `hsplit :
   PureCharPrimeSplitStatement`.  Reduction: `pureCharPrimeSplit_of_eOne_high pureCharPrimeEOne
   (pureCharPrimeEHigh_of_module hm)`.  The exponent-`p` half is now proved outright
   (`pureCharPrimeEOne`).  **LOUD: the module form is logically equivalent to
   `PureCharPrimeEHighStatement`.**  The converse is routine but proved only on paper.  It is
   smaller in proof content only.  `PureCharPrimeEHighStatement` is the case `H = ⊤` of
   `hsplit`, so with `pureCharPrimeEOne` proved, `hm` is also equivalent to `hsplit` on paper.
   It is not logically weaker.
2. `Absorption.SuslinLocalHorrocksStatement` replaces `hS : PolynomialSuslinStatement`.
   Reduction: `polynomialSuslin_of_oneVariable ∘ suslinOneVariable_of_patching ∘
   suslinPatching_of_localHorrocks`.  It is strictly weaker than
   `SuslinLocalGlobalQuillenStatement` (take `ε = 1`, `g = 1`) and smaller in content than `hS`.
   No converse is proved in Lean.
3. `ElemFP.VdKRowExtensionStatement` replaces `hdiag : PolyK2StabRangeDiagStatement`.
   Reduction: `polyK2StabRangeDiag_of_vdkRowExtension`.  **LOUD: the new gap is logically
   STRONGER than `hdiag`.**  It gives injective stability on all of `K₂`, not only on `ker ev₀`.
   It is smaller in proof content only.  It is true (Bass, van der Kallen).
4. `ElemFP.PolyK2CubeNilLocalStatement` replaces `hone : PolyK2OneVarNilStatement`.
   Reduction: `polyK2OneVarNil_of_cubeLocal`.  **LOUD: equivalent to `hone`.**  Both directions
   are proved in Lean (`polyK2CubeNilLocal_of_cubeNil` and the nilpotent-position bridges).
   It is smaller in proof content only.
5. `ElemFP.FieldK2.BruhatBigCellStatement` replaces `hfield : FieldK2VanishingStatement`.
   Reduction: `FieldK2.fieldK2Vanishing_of_bruhatBigCell`.  It is smaller in content (no
   action or faithfulness argument).  No converse is proved in Lean.  It is true (`K₂(F_p) = 0`
   plus the LDU factorization).
6. `ElemFPCharZero.CharZeroK2PosStabGenStatement` and
7. `ElemFPCharZero.CharZeroK2CubeGapPosStatement` together replace
   `hK2 : CharZeroStableK2FGStatement`.  Reduction: `charZeroStableK2FG_of_basePos_of_cubeGapPos
   (charZeroK2BasePos_of_stabGen hgen) hcube`.  This splits one gap into a base gap and a cube
   gap.  `hgen` is smaller in content than `CharZeroK2BasePosFGStatement`, with no converse
   proved.  **LOUD: `hcube` is equivalent to `CharZeroK2NilGapStatement`**
   (`charZeroK2CubeGapPos_of_nilGap` and `charZeroK2NilGap_of_cubeGapPos` are both proved).
   So the split is smaller in content than `hK2`, not logically weaker.
   Both are true (van der Kallen, Tate).
8. `Envelope.HigmanVSwapSectionStatement` replaces `hV : HigmanVFinSectionStatement`.
   Reduction: `higmanVFinSection_of_swapSection`.  It is smaller in content (Higman).  No
   converse is proved in Lean.  The same `hswap` also feeds item 9 via
   `higmanVFP_of_finSection`.
9. `Envelope.RNRelatorsFiniteCoreStatement` replaces `hcore : RNFreeSectionCoreStatement`.
   Reduction: `rnFreeSectionCore_of_normalForm (higmanVFP_of_finSection ...)
   (rnNormalFormRelators_of_finiteCore hrel)`.  **LOUD: `hrel` is equivalent to
   `RNNormalFormRelatorsStatement` on paper** (take `R₀ = R`, `F = E = ∅`).  It is smaller in
   content only.  The step from normal-form relators to `hcore` (given Higman's `V` f.p.) is
   proved.
10. `Envelope.GenTorsionVPerfectStatement` replaces `hfi : RNCommutatorFiniteIndexStatement`.
    Reduction: `rnFiniteIndex_of_vPerfect`.  It is smaller in content.  It is true, since
    `V_{2|X|,1}` is simple and perfect (Higman).

**Truth check.**  Each of the 10 Statements is true by the classical results cited above.
None of them is proved here.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The metabelian pieces node from the frontier-three linearity and linear-host gaps (items
1–7 of the module docstring). -/
theorem metabelianPiecesStatement_of_frontierThree
    (hm : Coprimary.PureCharPrimeEHighModuleStatement)
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hbruhat : ElemFP.FieldK2.BruhatBigCellStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement) :
    Products.MetabelianPiecesStatement :=
  metabelianPiecesStatement_of_frontierTwo_zeroClosed
    (Coprimary.pureCharPrimeSplit_of_eOne_high Coprimary.pureCharPrimeEOne
      (Coprimary.pureCharPrimeEHigh_of_module hm))
    (Absorption.polynomialSuslin_of_oneVariable
      (Absorption.suslinOneVariable_of_patching (Absorption.suslinPatching_of_localHorrocks hH)))
    (ElemFP.polyK2StabRangeDiag_of_vdkRowExtension hvdk)
    (ElemFP.polyK2OneVarNil_of_cubeLocal hloc)
    (ElemFP.FieldK2.fieldK2Vanishing_of_bruhatBigCell hbruhat)
    (ElemFPCharZero.charZeroStableK2FG_of_basePos_of_cubeGapPos
      (ElemFPCharZero.charZeroK2BasePos_of_stabGen hgen) hcube)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.metabelianPiecesStatement_of_frontierThree

/-- **The root from the ten frontier-three gaps**: finitely presented metabelian groups satisfy
the Boone–Higman conjecture, given the ten Statements listed in the module docstring. -/
theorem finitelyPresentedMetabelianStatement_of_frontierThree
    (hm : Coprimary.PureCharPrimeEHighModuleStatement)
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hbruhat : ElemFP.FieldK2.BruhatBigCellStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : Envelope.HigmanVSwapSectionStatement)
    (hrel : Envelope.RNRelatorsFiniteCoreStatement)
    (hperf : Envelope.GenTorsionVPerfectStatement) : FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_of_frontierTwo_zeroClosed
    (Coprimary.pureCharPrimeSplit_of_eOne_high Coprimary.pureCharPrimeEOne
      (Coprimary.pureCharPrimeEHigh_of_module hm))
    (Absorption.polynomialSuslin_of_oneVariable
      (Absorption.suslinOneVariable_of_patching (Absorption.suslinPatching_of_localHorrocks hH)))
    (ElemFP.polyK2StabRangeDiag_of_vdkRowExtension hvdk)
    (ElemFP.polyK2OneVarNil_of_cubeLocal hloc)
    (ElemFP.FieldK2.fieldK2Vanishing_of_bruhatBigCell hbruhat)
    (ElemFPCharZero.charZeroStableK2FG_of_basePos_of_cubeGapPos
      (ElemFPCharZero.charZeroK2BasePos_of_stabGen hgen) hcube)
    (Envelope.higmanVFinSection_of_swapSection hswap)
    (Envelope.rnFreeSectionCore_of_normalForm
      (Envelope.higmanVFP_of_finSection (Envelope.higmanVFinSection_of_swapSection hswap))
      (Envelope.rnNormalFormRelators_of_finiteCore hrel))
    (Envelope.rnFiniteIndex_of_vPerfect hperf)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierThree

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
