import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwoBase
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring, part 4: the metabelian root from the ten remaining gaps (lane `bh-met-45`)

`ChainWiredFrontier.finitelyPresentedMetabelianStatement_of_frontier` takes fourteen gap
Statements.  Four are now proved unconditionally and are discharged:

* `CharZeroHost.FGSubringCoordinatesStatement` by `CharZeroHost.fgSubringCoordinates`
  (`CharZeroCoordsAssembly.lean:42`);
* `Envelope.RNCompressStatement` by `Envelope.rnCompressStatement_holds`
  (`EnvelopeSimpleCompressClose.lean:74`);
* `Envelope.RNFragmentsStatement` by `Envelope.rnFragmentsStatement_proof`
  (`EnvelopeSimpleFragStep.lean:149`);
* `Envelope.RNWreathEmbedStatement` by `Envelope.rnWreathEmbed` (`EnvelopeWreathEmbed.lean:126`).

The first three leaves are wired in `ChainWiredFrontierTwoBase` (which does not import
`EnvelopeSimpleFragStep`); this module adds fragmentation.

**The remaining frontier (10 Statements)**, with the smallest on-disk reduction of each.
Paths are relative to `GroupApproximation/BooneHigman/Metabelian/`.

1. `Coprimary.PureCharPrimeSplitStatement` (`PureCharPrimeSplit.lean:54`).  Residual split
   stated in `PureCharPrimeEStatement.lean`: `PureCharPrimeEOneStatement` (`:47`, exponent `p`,
   module-theoretic; consumed by `exists_gl_of_exponent_prime`, `PureCharPrimeEOne.lean:73`) and
   `PureCharPrimeEHighStatement` (`:62`, exact exponent `p ^ e`, `e ≥ 2`).  The announced
   reduction `pureCharPrimeSplit_of_eOne_high` (module `PureCharPrimeESplit`) is not on disk.
2. `Coprimary.PureCharLinearityZeroStatement` (`PureCharSplit.lean:32`).  Reduced to
   `Coprimary.TorsionFreeModuleLinearityStatement` (`PureCharZeroStatement.lean:38`) by
   `pureCharLinearityZero_of_torsionFreeModuleLinearity` (`PureCharZeroStatement.lean:58`).
3. `Absorption.PolynomialSuslinStatement` (`AbsorptionEndpoint.lean:63`).  Reduced to the
   one-variable step `Absorption.SuslinOneVariableStatement` (`AbsorptionSuslinReduction.lean:42`)
   by `polynomialSuslin_of_oneVariable` (`AbsorptionSuslinReduction.lean:79`).
4. `ElemFP.PolyK2StabRangeDiagStatement` (`ElemFPK2StabRange.lean:67`).  No smaller reduction;
   the per-prime reformulation `polyK2StabRangeDiag_iff_forall_over`
   (`ElemFPCharZeroK2NilCharP.lean:45`) is an equivalence.
5. `ElemFP.PolyK2OneVarNilStatement` (`ElemFPK2OneVar.lean:43`).  Reformulated as the cube gap
   `ElemFP.PolyK2CubeNilStatement` (`ElemFPK2OneVarNilCube.lean:124`) by
   `polyK2OneVarNil_of_cubeNil` (`ElemFPK2OneVarNilCube.lean:150`).  Through
   `PolyK2NilPosStatement` (`polyK2CubeNil_of_nilPos`, `ElemFPK2OneVarNilCube.lean:141`, and
   `polyK2NilPos_of_oneVar`, `ElemFPK2OneVar.lean:103`) the cube gap is logically
   equivalent; it differs only in form.
6. `ElemFP.FieldK2VanishingStatement` (`ElemFPK2Split.lean:55`).  No reduction on disk.
7. `ElemFPCharZero.CharZeroStableK2FGStatement` (`ElemFPCharZeroEndpoint.lean:65`).  Reduced by
   `charZeroStableK2FG_of_base_of_nilGap` (`ElemFPCharZeroK2NilEndpoint.lean:102`) to
   `CharZeroK2BaseFGStatement` (`ElemFPCharZeroK2Split.lean:100`) and
   `CharZeroK2NilGapStatement` (`ElemFPCharZeroK2NilEndpoint.lean:63`); the base part further to
   `CharZeroK2BasePosFGStatement` (`ElemFPCharZeroK2BaseEndpoint.lean:65`) by
   `charZeroK2BaseFG_of_pos` (`ElemFPCharZeroK2BaseEndpoint.lean:71`).  The nil gap is equivalent
   to `CharZeroK2NilPosStatement` (`charZeroK2NilGap_of_nilPos`,
   `ElemFPCharZeroK2NilEndpoint.lean:87`).
8. `Envelope.HigmanVFinSectionStatement` (`EnvelopeHigmanVSection.lean:49`).  No reduction on
   disk; it gives `HigmanVFPStatement` by `higmanVFP_of_finSection`
   (`EnvelopeHigmanVSection.lean:77`).
9. `Envelope.RNFreeSectionCoreStatement` (`EnvelopeHigmanVStatement.lean:43`).  Reduced to
   `Envelope.RNNormalFormRelatorsStatement` (`EnvelopeNormalFormSection.lean:55`), given
   `HigmanVFPStatement` (which item 8 supplies), by `rnFreeSectionCore_of_normalForm`
   (`EnvelopeNormalFormSection.lean:96`).
10. `Envelope.RNCommutatorFiniteIndexStatement` (`EnvelopeSplit.lean:51`).  No reduction on disk.

These reductions are recorded, not plugged in: the hypotheses below are exactly the ten
Statements above, in the argument order of `finitelyPresentedMetabelianStatement_of_frontier`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The self-similar envelope from finite presentation (`hV`, `hcore`) and finite index (`hfi`);
compression, fragmentation and the wreath embedding are proved. -/
theorem fpSelfSimilarEnvelope_of_frontierTwo (hV : Envelope.HigmanVFinSectionStatement)
    (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) :
    Products.FPSelfSimilarEnvelopeStatement :=
  fpSelfSimilarEnvelope_of_frontierTwoBase hV hcore hfi Envelope.rnFragmentsStatement_proof

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.fpSelfSimilarEnvelope_of_frontierTwo

/-- **The root from the remaining frontier**: finitely presented metabelian groups satisfy the
Boone–Higman conjecture, given the ten gap Statements listed in the module docstring (items 1–2
linearity, 3–7 linear hosts, 8–10 the self-similar envelope). -/
theorem finitelyPresentedMetabelianStatement_of_frontierTwo
    (hsplit : Coprimary.PureCharPrimeSplitStatement)
    (hzero : Coprimary.PureCharLinearityZeroStatement) (hS : Absorption.PolynomialSuslinStatement)
    (hdiag : ElemFP.PolyK2StabRangeDiagStatement) (hone : ElemFP.PolyK2OneVarNilStatement)
    (hfield : ElemFP.FieldK2VanishingStatement)
    (hK2 : ElemFPCharZero.CharZeroStableK2FGStatement)
    (hV : Envelope.HigmanVFinSectionStatement) (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) : FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_of_frontierTwoBase hsplit hzero hS hdiag hone hfield hK2
    hV hcore hfi Envelope.rnFragmentsStatement_proof

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierTwo

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
