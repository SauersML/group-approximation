import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontier
import GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsAssembly
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleCompressClose
import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreathEmbed
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring, part 4a: the frontier with the closed leaves discharged (lane `bh-met-45`)

`ChainWiredFrontier.finitelyPresentedMetabelianStatement_of_frontier` takes fourteen gap
Statements.  Three of them are now proved unconditionally on disk and are discharged here:

* `CharZeroHost.FGSubringCoordinatesStatement`: `CharZeroHost.fgSubringCoordinates`
  (`CharZeroCoordsAssembly.lean:42`);
* `Envelope.RNCompressStatement`: `Envelope.rnCompressStatement_holds`
  (`EnvelopeSimpleCompressClose.lean:74`);
* `Envelope.RNWreathEmbedStatement`: `Envelope.rnWreathEmbed` (`EnvelopeWreathEmbed.lean:126`).

The fourth closed leaf, `Envelope.rnFragmentsStatement_proof : RNFragmentsStatement`
(`EnvelopeSimpleFragStep.lean:149`), is discharged in `ChainWiredFrontierTwo`; this module does
not import it, so that the wiring of the three leaves above does not depend on that module.

No new mathematics: every proof below is a term application of on-disk declarations.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The characteristic-zero linear host from Suslin's theorem and finite generation of stable
`K₂`; the f.g.-subring coordinates are `CharZeroHost.fgSubringCoordinates`. -/
theorem charZeroLinearHostStatement_of_frontierTwo (hS : Absorption.PolynomialSuslinStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : CharZeroLinearHostStatement :=
  charZeroLinearHostStatement_of_frontier hS CharZeroHost.fgSubringCoordinates hK2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.charZeroLinearHostStatement_of_frontierTwo

/-- The linear host node from the remaining linear-host gaps. -/
theorem linearHostStatement_of_frontierTwo (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : Products.LinearHostStatement :=
  linearHostStatement_of_frontier hS hdiag hone hfield CharZeroHost.fgSubringCoordinates hK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.linearHostStatement_of_frontierTwo

/-- The metabelian pieces node from the remaining linearity and linear-host gaps. -/
theorem metabelianPiecesStatement_of_frontierTwo (hsplit : Coprimary.PureCharPrimeSplitStatement)
    (hzero : Coprimary.PureCharLinearityZeroStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement) : Products.MetabelianPiecesStatement :=
  metabelianPiecesStatement_of_frontier hsplit hzero hS hdiag hone hfield
    CharZeroHost.fgSubringCoordinates hK2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.metabelianPiecesStatement_of_frontierTwo

/-- The self-similar envelope from finite presentation, finite index and fragmentation;
compression is `Envelope.rnCompressStatement_holds` and the wreath embedding is
`Envelope.rnWreathEmbed`. -/
theorem fpSelfSimilarEnvelope_of_frontierTwoBase (hV : Envelope.HigmanVFinSectionStatement)
    (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) (hF : Envelope.RNFragmentsStatement) :
    Products.FPSelfSimilarEnvelopeStatement :=
  fpSelfSimilarEnvelope_of_frontier hV hcore hfi Envelope.rnCompressStatement_holds hF
    Envelope.rnWreathEmbed

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.fpSelfSimilarEnvelope_of_frontierTwoBase

/-- The root from eleven gap Statements (the fourteen of `ChainWiredFrontier` minus
f.g.-subring coordinates, compression and the wreath embedding). -/
theorem finitelyPresentedMetabelianStatement_of_frontierTwoBase
    (hsplit : Coprimary.PureCharPrimeSplitStatement)
    (hzero : Coprimary.PureCharLinearityZeroStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement)
    (hV : Envelope.HigmanVFinSectionStatement) (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) (hF : Envelope.RNFragmentsStatement) :
    FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_of_frontier hsplit hzero hS hdiag hone hfield
    CharZeroHost.fgSubringCoordinates hK2 hV hcore hfi Envelope.rnCompressStatement_holds hF
    Envelope.rnWreathEmbed

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierTwoBase

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
