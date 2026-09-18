import GroupApproximation.BooneHigman.Metabelian.ChainWiredEnvelope
import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontier
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring with simplicity of `[V, V]` discharged (lane `bh-met-49`)

No theorem in `ChainWired*.lean` takes `Envelope.RNDisplaceCompressStatement` as a single
hypothesis.  It enters in bundled form, as the pair `hC : Envelope.RNCompressStatement`,
`hF : Envelope.RNFragmentsStatement` fed to `Envelope.rnDisplaceCompress_of_compress_fragments`,
in exactly two theorems:

* `fpSelfSimilarEnvelope_of_frontier` (`ChainWiredEnvelope.lean:57`);
* `finitelyPresentedMetabelianStatement_of_frontier` (`ChainWiredFrontier.lean:118`).

The primed variants below drop `hC` and `hF` and keep every other hypothesis identical (same
names, types and order).  Simplicity is supplied by
`Envelope.rnCommutatorSimpleStatement_holds` (`EnvelopeSimpleClosed`), which is
`rnCommutatorSimple_of_prime (rnCommutatorSimple_of_gap rnDisplaceCompressStatement_holds)`.

`fpSelfSimilarEnvelope_of_frontierTwoBase` and
`finitelyPresentedMetabelianStatement_of_frontierTwoBase` (`ChainWiredFrontierTwoBase.lean`) take
only `hF`; their variants with `hF` removed are already on disk with identical hypotheses and
conclusions, as `fpSelfSimilarEnvelope_of_frontierTwo` and
`finitelyPresentedMetabelianStatement_of_frontierTwo` (`ChainWiredFrontierTwo.lean`), so they are
not duplicated here.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- **The self-similar envelope** from finite presentation (`hV`, `hcore`), finite index
(`hfi`) and the wreath embedding (`hw`); simplicity of `[V, V]` is
`Envelope.rnCommutatorSimpleStatement_holds`. -/
theorem fpSelfSimilarEnvelope_of_frontier' (hV : Envelope.HigmanVFinSectionStatement)
    (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement)
    (hw : Envelope.RNWreathEmbedStatement) : Products.FPSelfSimilarEnvelopeStatement :=
  Envelope.fpSelfSimilarEnvelope_of_rnEnvelope
    (Envelope.rnEnvelope_of_four
      (rnFinitelyPresented_of_prime
        (Envelope.rnFinitelyPresented_of_freeSection
          (Envelope.rnFreeSection_of_finSection_core hV hcore)))
      hfi Envelope.rnCommutatorSimpleStatement_holds hw)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.fpSelfSimilarEnvelope_of_frontier'

/-- **The root from the open frontier minus simplicity**: the hypotheses of
`finitelyPresentedMetabelianStatement_of_frontier` with `hC` and `hF` removed. -/
theorem finitelyPresentedMetabelianStatement_of_frontier'
    (hsplit : Coprimary.PureCharPrimeSplitStatement)
    (hzero : Coprimary.PureCharLinearityZeroStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hfg : CharZeroHost.FGSubringCoordinatesStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement)
    (hV : Envelope.HigmanVFinSectionStatement) (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement)
    (hw : Envelope.RNWreathEmbedStatement) : FinitelyPresentedMetabelianStatement :=
  Products.finitelyPresentedMetabelianStatement_of_pieces
    (metabelianPiecesStatement_of_frontier hsplit hzero hS hdiag hone hfield hfg hK2)
    (fpSelfSimilarEnvelope_of_frontier' hV hcore hfi hw)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontier'

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
