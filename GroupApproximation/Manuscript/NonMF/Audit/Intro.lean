import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Analysis.LanceMaximalNuclear
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Analysis.WitnessGroupNonamenable
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Leavitt.BinaryLeavittAllRanksUnits
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Leavitt.UniversalOneSidedPairRing
import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Manuscript.NonMF.PriorWorkConnesEmbedding
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedTheorem
import GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences
import GroupApproximation.Manuscript.NonMFSentences.IntroSentences
import GroupApproximation.Manuscript.NonMFSentences.IntroUnitGroupSentences
import GroupApproximation.Manuscript.NonMFSentences.KorchaginFullSequenceSentence
import GroupApproximation.Manuscript.NonMFSentences.LeavittKOneFormulaSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.CountableNonMF
import GroupApproximation.Manuscript.OneSidedMFRadical.CurrentManuscriptDefinitionRepairs
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.IntroductionClaimSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransportSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientCanonicalKOne
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof
import GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarWNotNuclearUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectFunctorial
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceCompressionCriterionIntroductionClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceIntroductionDefinitionsClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceLeavittHeadlineIntroductionClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportCommutantEquality
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.StrongConvergenceMF

/-!
# Audit gate: abstract and Introduction

`non_mf_groups_exist.tex` lines 1–345.

Every census row in this range with status `formalized` or `definition` names Lean
declarations, and so does every structural or attribution row that carries a mathematical
claim.  Each named declaration is audited below.  A widened axiom closure, or a declaration
that has been lost or renamed, is then a build error in this module.

* `#audit_closed_axioms` is used on named-proposition endpoints, whose type is a
  `def … : Prop` rather than a leading binder.
* `#audit_axioms` is used on every other carrier: definitions, and sentence-level lemmas
  whose hypotheses are the printed setup or the conclusions of earlier sentences.

Each group of lines names its tex line and census row id.  A declaration named by several
rows is audited once, at its first row.

Rows with status `partial` belong to lanes still working on the walls and are not gated
here: `a16637da7249` (tex line 66), `61827aea7807` (tex line 187), `0f22bdbc4184`
(tex line 285) and `dce7a9ff4e83` (tex line 291).
-/

/-! ## L66 `113e60b5f202` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion

/-! ## L66 `3393c0cf411c` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNotEveryCountableGroupIsMF

/-! ## L87 `88e8012cb87e` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroductionMFDefinition

/-! ## L94 `6201111b83a0` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalizedMFModelSeparation

/-! ## L99 `837b7cffa562` (formalized) -/

#audit_axioms GroupApproximation.IsStronglyOperatorMF
#audit_axioms GroupApproximation.leftRegularNorm
#audit_axioms GroupApproximation.IsStronglyOperatorMF.isOperatorMF
#audit_axioms GroupApproximation.not_isStronglyOperatorMF_of_not_isOperatorMF

/-! ## L99 `8d0b87a46a51` (definition) -/

#audit_axioms GroupApproximation.IsCDEOperatorMF
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence11_MFDefinition

/-! ## L99 `b1b04e376fe7` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.KorchaginSentence.manuscriptSentence_korchaginFullSequenceSeparation

/-! ## L112 `ad33e493e32f` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroductionSeparableCStarAlgebraIsMFDef

/-! ## L112 `be1769283b2f` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.manuscriptSentence_boundedProductsNullIdeal
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedBoundedProductsNullIdeal
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.zero_mem_normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.add_mem_normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.neg_mem_normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.mul_left_mem_normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.mul_right_mem_normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.star_mem_normNullSequences
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.isClosed_normNullSequences

/-! ## L112 `d31180a98ce2` (definition) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CoronaHomomorphism

/-! ## L122 `10e027681ba5` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_mfRadicalFormula

/-! ## L122 `f2a05ccf5990` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_mfRadicalQuotientIsMFAndLargest

/-! ## L134 `651e122a919e` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.manuscriptSentence_cliffordWitnessGroup
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedCliffordWitnessGroup
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedGamma
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedV
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedX
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedW
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.cliffordLamp_lamp_ne_one
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.cliffordLamp_presentation

/-! ## L134 `9930600167a4` (formalized) -/

#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget

/-! ## L148 `8766dc520cfb` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroUnitGroupSentences.manuscriptSentence_introUnitGroup
#audit_closed_axioms GroupApproximation.UniversalLeavitt.manuscriptSentence_glElUnitsAllRanks
#audit_closed_axioms GroupApproximation.UniversalLeavitt.manuscriptSentence_rightModuleSelfSimilarity

/-! ## L156 `56d73653208a` (definition) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefectSet
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence40_printedDefect_display

/-! ## L156 `b671ae1aab2b` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.c_commutes_corner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_compresses_corner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_c_commutator_ell

/-! ## L156 `ec81a8c16b64` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.manuscriptSentence_commutatorConvention
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroConventionSentences.PrintedCommutatorConvention

/-! ## L156 `effc40395f2b` (definition) -/

#audit_axioms GroupApproximation.compressionSet
#audit_axioms GroupApproximation.mem_compressionSet_iff

/-! ## L177 `51077cfd1fa7` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFunctorial

/-! ## L187 `a700a5798fd5` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_adIsAsymptoticallyMultiplicativeUnitaryFamily
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_adIsTwoLipschitz
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_adClassesFormCoronaHomomorphism
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_compressorClassAndKazhdanProjectionImage
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarKazhdanProjectionOrder
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormMatrixCoronaStableFinite
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_defectAsymptoticallyTrivialInHS
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectShadowInclusion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportCommutantEquality
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.boundedHSCommutant
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_compressorSatisfiesProjectionOrder
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_stableFinitenessGivesProjectionEquality
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_coronaKazhdanComplementIsInvariantCorner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_commutatorHilbertSchmidtVanishing

/-! ## L187 `e63d12558c72` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_nontrivialCoronaHomCompressesToKillingCorner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_propertyTUpgradesHSTrivialityToOperatorNorm
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute.manuscriptPrintedCentralCoronaCorner

/-! ## L207 `29d7a8ccf93a` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_universalProperty
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_imageOfBNormallyGeneratesELn
#audit_axioms GroupApproximation.UniversalPair.UniversalPairRing

/-! ## L207 `6b5d4b5c3081` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_compressorMatrix
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_intertwine
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_defectIsEverything

/-! ## L207 `91310d39561c` (definition) -/

#audit_axioms GroupApproximation.elementaryUnit
#audit_axioms GroupApproximation.elementaryGroup
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence54_elementaryRoot_and_elementaryGroup

/-! ## L221 `0317786bea4d` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptPrintedFullDefectRingProgrammeAllCharacteristics

/-! ## L225 `4bf35a8f555d` (definition) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences.manuscriptSentence_ringRelations

/-! ## L234 `63c2a4ca81c4` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline.manuscriptUnitGroupHeadline

/-! ## L243 `0e0ede2715c4` (formalized) -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAtBaseRing
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne

/-! ## L243 `2d6ab84875e0` (formalized) -/

#audit_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptSentence_unitGroupQuotient

/-! ## L251 `cd72291264e4` (formalized) -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTrace

/-! ## L258 `2a97fb901bad` (formalized) -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF

/-! ## L258 `a96c09324a87` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_maximalCStarWNotNuclear
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarNotNuclearOfNotAmenable
#audit_axioms GroupApproximation.LanceMaximal.isAmenable_of_isNuclearCStarAlgebra_maximalGroupCStar
#audit_axioms GroupApproximation.WitnessGroupNonamenable.witnessGroup_not_isAmenable

/-! ## L258 `cd3ea932e46a` (formalized) -/

#audit_axioms GroupApproximation.AmenableTraceTheorem.manuscriptMFNotClosedUnderIntSemidirect

/-! ## L258 `f969236a73d8` (formalized) -/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptWSoficFromLocallyRFExtension

/-! ## L280 `abb56744db26` (structural) -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.PrintedTorsionFreeTheorem

/-! ## L291 `27e0c2f96db3` (attribution) -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TheoremC.LiteratureInputs
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.saturation

/-! ## L298 `6edef6dc2d68` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF

/-! ## L298 `abfcbcb3af2b` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMF.PriorWork.printedNegativeConnesEmbeddingSentence

/-! ## L324 `523f02126056` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_kazhdanInequalityKillsCornerOnDefect
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionDefect
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute.manuscriptNormalKazhdanRadical_printedRoute
