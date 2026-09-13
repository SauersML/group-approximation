import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Analysis.AdjointDefectEstimate
import GroupApproximation.Analysis.CollapseProjectionLift
import GroupApproximation.Analysis.CoronaProjectionOrder
import GroupApproximation.Analysis.KazhdanProjectionOneSidedOrder
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.MatrixCoronaDedekindFinite
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Analysis.MaximalCStarProperCompression
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.NormalKazhdanUltraproduct
import GroupApproximation.Analysis.ProperIsometryFromCompression
import GroupApproximation.Analysis.ProperIsometryStrictOrder
import GroupApproximation.Analysis.QuasiRegularWitness
import GroupApproximation.Analysis.ResiduallyFiniteDimensionalMF
import GroupApproximation.Analysis.StrictCompressionFromPrinted
import GroupApproximation.Manuscript.NonMFSentences.CentralCoronaCornerRanks
import GroupApproximation.Manuscript.NonMFSentences.CompressionSentencesA
import GroupApproximation.Manuscript.NonMFSentences.CompressionSentencesB
import GroupApproximation.Manuscript.NonMFSentences.CompressionSentencesB2
import GroupApproximation.Manuscript.NonMFSentences.DyadicReductionSeparation
import GroupApproximation.Manuscript.NonMFSentences.HSNullNormalSubgroupSentences
import GroupApproximation.Manuscript.NonMFSentences.HSOperatorNormGapSentences
import GroupApproximation.Manuscript.NonMFSentences.KazhdanProjectionExistenceSentence
import GroupApproximation.Manuscript.NonMFSentences.MFRadicalQuotientBlockSumSentences
import GroupApproximation.Manuscript.NonMFSentences.NormalKazhdanUltrafilterRoute
import GroupApproximation.Manuscript.NonMFSentences.TransportCharacterizationIffSentence
import GroupApproximation.Manuscript.OneSidedMFRadical.CanonicalSector
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProvenanceData
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrderLiteral
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransport
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransportSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.MaxInfiniteConverseRemark
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.PartialClosureAnalysisTwo
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedForms
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedSectorProof
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceAdjointCoronaHomClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceCompressionCriterionIntroductionClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceNormalKazhdanClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceTransportClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceTransportCoreSetupClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceTransportPreliminariesClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFinitenessSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportAssembly
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportKazhdanProjection
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCommutation
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportSigmaTilde
import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.AffineHNNBaseRealization
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Sofic.OpAlmostRepresentation
import GroupApproximation.Sofic.OpToHSShadowResidual

/-!
# Audit gate: `sec:compression-radical` (One-sided compression)

`non_mf_groups_exist.tex` lines 346–784.

Every census row in this range with status `formalized` or `definition` names Lean
declarations, and so does every structural or attribution row that carries a mathematical
claim.  Each named declaration is audited below.  A widened axiom closure, or a declaration
that has been lost or renamed, is then a build error in this module.

* `#audit_closed_axioms` is used on named-proposition endpoints, whose type is a
  `def … : Prop` rather than a leading binder.
* `#audit_axioms` is used on every other carrier: definitions, and sentence-level lemmas
  whose hypotheses are the printed setup or the conclusions of earlier sentences.

Each group of lines names its tex line and census row id.  A declaration named by several
rows is audited once, at its first row; declarations already audited by
`GroupApproximation.Manuscript.NonMF.Audit.Intro` are not repeated.

No row in this range has status `partial`.
-/

/-! ## L352 `3bd1b6ab184a` (formalized) -/

#audit_axioms GroupApproximation.isCDEOperatorMF_of_faithful_corona_map

/-! ## L352 `a8e4ac99b640` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.allMFTargetsKill_iff_allCoronasKill

/-! ## L352 `bd2989c81dc3` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_appliesToMaximalCanonicalMap
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_appliesToReducedCanonicalMap

/-! ## L364 `46d40014ee9e` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_coronaImageIsCountableMF

/-! ## L364 `6c597e046078` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_composeMFHomWithCoronaEmbeddingSameKernel

/-! ## L364 `bee886268f33` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_nonunitalCoronaHomInjectiveOnG

/-! ## L372 `07de7e8a943a` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_blockSumFamily
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_mfRadicalQuotientResidualTrivial

/-! ## L383 `240357aed76a` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount

/-! ## L383 `b1b62a9e3c06` (structural) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_asymptoticRepresentationHasNoExactCommutant

/-! ## L383 `fd2cafafd8fa` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_exactRepresentationCommutantDimensionCount

/-! ## L393 `399d33df9009` (definition) -/

#audit_axioms GroupApproximation.hsNorm

/-! ## L398 `629f562df6bc` (definition) -/

#audit_axioms GroupApproximation.OpAlmostRepresentation

/-! ## L404 `b093f3c88101` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_hsNullNormalSubgroupPrintedRoute
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.printedHSNullSubgroup
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.printedHSNullSubgroup_normal
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.mem_printedHSNullSubgroup_iff_mem_hsKernel

/-! ## L413 `db30dea6e7f0` (definition) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedCommutant.printedCTwo

/-! ## L422 `186ab929187a` (definition) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IsCStarFinite
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IsCStarStablyFinite

/-! ## L422 `630db09c6f46` (definition) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.adSequence
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_adSequenceBijective

/-! ## L429 `6b1c6779ed70` (formalized) -/

#audit_axioms GroupApproximation.NormMatrixCStarCorona

/-! ## L433 `a594de997cbe` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptStableFinite

/-! ## L433 `da52971fd39a` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentences114_115_normMatrixCorona_stableFinite

/-! ## L439 `5e9b44d1c0bb` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_70c4de929477
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_9b9e5b396d6f

/-! ## L439 `6b308543eb28` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_0ac3ff393cfe
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_8461ba613634
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_974e2b57e3ef
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_ee3d6cbf975d
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_fc7ae023c534

/-! ## L439 `daecb970c06a` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_993df6a79c44
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_36cd63cf2803_stablyFinite
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.MatrixAmplificationCoronaIsomorphism
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.sentence_b21cf7f0f627

/-! ## L439 `fc6ea69c0036` (definition) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.stableFiniteCorona

/-! ## L451 `86ee71463acf` (definition) -/

#audit_axioms GroupApproximation.MaximalCStarKazhdanProjection.KazhdanData.projection
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_kazhdanProjection
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.kazhdanProjection_central

/-! ## L458 `1ff4a5b717b2` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence124_maximalCStarKazhdanProjection

/-! ## L458 `9bd4e2f1eaa1` (structural) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarKazhdanProjectionOrder
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.OneSidedKazhdanProjectionOrder

/-! ## L458 `bad6f3c843a4` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanProjectionOrder
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptLiteralMaximalCStarKazhdanProjectionOrder

/-! ## L467 `7cf7dd61da4f` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence126_representedKazhdanProjection_range

/-! ## L467 `ac2c96deddba` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence129_faithfulRepresentation_reflectsProjectionOrder
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.le_of_le_in_faithful_rep
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_movedFixedSpaceInclusionAndProjectionOrder

/-! ## L467 `bdceff578c1b` (definition) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedFaithfulNondegenerateRepresentation

/-! ## L467 `ea315c314c25` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence127_inverseUnitary_preserves_fixedSpace
#audit_axioms GroupApproximation.KazhdanProjectionOneSidedOrder.symm_mem_invariantSubmodule_of_compresses
#audit_axioms GroupApproximation.KazhdanProjectionOneSidedOrder.symm_mem_of_conj_mem

/-! ## L479 `5292e3a80968` (structural) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.OneSidedKazhdanTransport
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransport

/-! ## L479 `7229247f62b3` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportPackage
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportAnyAmbient
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedRoute.manuscriptPrintedTransportHS

/-! ## L490 `765fe31bdd7a` (formalized) -/

#audit_axioms GroupApproximation.l2_opNorm_conjDouble_sub_le_two
#audit_axioms GroupApproximation.opNorm_adConj_sub_le_two_mul

/-! ## L494 `a940b20e39ec` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportSigmaTilde.tendsto_adMatrix_defect

/-! ## L503 `6bf30ab286b0` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportSigmaTilde.sigmaTilde

/-! ## L503 `87f873612529` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCommutation.exists_projectionData

/-! ## L503 `a6985193463f` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_sigmaTildeIsHomomorphism
#audit_axioms GroupApproximation.OpAlmostRepresentation.card_adjoint_naturalizeCoordinates_model
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptAdjointCoordinateSquareAndExactCoronaHom

/-! ## L511 `3df2cd0a86ce` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportCharacterizationIffSentence.manuscriptSentence_printedCTwoIffProjectionAbsorbs

/-! ## L516 `e702793d4e6d` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportKazhdanProjection.exists_combination_close

/-! ## L522 `36a9ae1219bf` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportKazhdanProjection.limsup_norm_sub_combSeq_lt

/-! ## L531 `a5a02a73b909` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization.tendsto_hsNorm_applyOp_projection_sub

/-! ## L539 `734283523715` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization.tendsto_norm_adMatrix_mul_projection_sub
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization.isHSAsymptoticallyCentral_of_tendsto

/-! ## L552 `5c8aa0403a34` (definition) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.adjointCoronaHom

/-! ## L552 `916db87815b7` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedRoute.tendsto_hsNorm_applyOp_projection_sub_of

/-! ## L552 `fa1ec5f45603` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCommutation.commute_sigmaB_projection

/-! ## L572 `67ab9f71cba9` (structural) -/

#audit_axioms GroupApproximation.mem_opToHSShadowResidual_iff
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionDefectHSInvisible
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible

/-! ## L572 `c36b6021a802` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectHS
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectHS
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.HSVanishes

/-! ## L583 `310f6df94cdf` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_conjugatedCentralizerStaysInPrintedCommutant

/-! ## L583 `a6988bc68f49` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_hsCommutatorVanishesAndDefectIsHSTrivial

/-! ## L583 `acc79ac4eb5f` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_hsTrivialElementsFormNormalSubgroupWithDefect

/-! ## L596 `f4cdb1554874` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_hsSmallnessDoesNotBoundOperatorNorm
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.printedSignDiagonal

/-! ## L609 `c9d3bf1f96b3` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterionSentences.manuscriptSentence_cornerCompressionsAreOnlyApproximatelyUnitary

/-! ## L616 `2aa506733448` (structural) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCentralCoronaCorner

/-! ## L630 `4c8affbaad3c` (formalized) -/

#audit_axioms GroupApproximation.CollapseProjectionLift.exists_projection_lift

/-! ## L630 `6a04faf78706` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding.cornerEmbedSeq_cornerCompressSeq_apply
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding.norm_mk_cornerEmbedSeq
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding.cornerEmbedSeq_mul
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding.cornerEmbedSeq_star
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaEmbedding.cornerEmbedSeq_one_apply

/-! ## L630 `87860427644c` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute.exists_cornerUnitaries

/-! ## L630 `f494ded864dc` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_retainedCoordinatesAndRanks
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute.manuscriptSentence_retainedCoordinatesInfinite

/-! ## L647 `7778d54e679f` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanRadical
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.PrintedNormalKazhdan
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedNormalKazhdan

/-! ## L647 `efed62e83cca` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanPrintedRadical

/-! ## L656 `5abc59e0d8cc` (formalized) -/

#audit_axioms GroupApproximation.NormalKazhdanUltraproduct.nk_07_conjugate_proj
#audit_axioms GroupApproximation.NormalKazhdanUltraproduct.nk_07_commute_proj
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence_conjugatedProjectionRangesAgree

/-! ## L656 `9658ec21017b` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence171_maximalProjectionImageIsFixedProjection
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence171_maximalProjectionImageIsFixedProjection_allUniverses
#audit_axioms GroupApproximation.MaximalCStarKazhdanProjection.exists_kazhdanData
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProvenanceData

/-! ## L656 `a7997fb95c84` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute.manuscriptSentence_kazhdanProjectionImage

/-! ## L669 `0239ca7d2b5e` (definition) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.cornerCoronaUnitaryHom

/-! ## L669 `0c1ad4392d72` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_inducedCornerKazhdanProjectionZero

/-! ## L669 `2e9741292f4c` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCornerCoronaClass

/-! ## L669 `3e281c6ee4c3` (formalized) -/

#audit_axioms GroupApproximation.NormalKazhdanUltraproduct.nk_06_q_ne_zero
#audit_axioms GroupApproximation.NormalKazhdanUltraproduct.nk_06_rep_eq_one_of_q_eq_zero

/-! ## L680 `00691a0fd65c` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_ultrafilterTraceIsTracialStateOnCorona
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.norm_ultrafilterNormalizedTraceAdd_le
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_ultrafilterNormalizedTraceWellDefined

/-! ## L680 `54db830af92e` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute.manuscriptSentence_traceOfCombinationTendsTo

/-! ## L680 `5c6689ae5e75` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.ultrafilterNormalizedTraceCLM
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_ultrafilterNormalizedTraceIsWellDefinedTracialState

/-! ## L690 `377d3a03266b` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_trivialCharacterIsStateWithValues

/-! ## L690 `4e13d6e99e2d` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_ultrafilterTraceOfCornerUnitaryIsOne

/-! ## L690 `82dded1b13b3` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra

/-! ## L690 `fb1df1a24e3f` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_oneEqualsZeroContradiction

/-! ## L700 `7409ff7e2c5f` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptNormalKazhdanRadical_ultrafilterRoute

/-! ## L705 `2f041595e7a7` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence42_normalKazhdan_defect_le_radical
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCompressionCriterion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCompressionCriterion

/-! ## L705 `4bc46d4603fd` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompleteOneSidedCompressionCriterion

/-! ## L705 `50ca303a15db` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence43_nontrivial_defectKazhdan_obstructs_MF
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence44_full_defect_gives_full_radical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets

/-! ## L717 `4cd99c2ee1cb` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectNormalKazhdanRadical

/-! ## L729 `a45c53bf93dd` (formalized) -/

#audit_closed_axioms GroupApproximation.MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses

/-! ## L729 `e681972f7114` (formalized) -/

#audit_axioms GroupApproximation.QuasiRegularWitness.baseVector_apply_base
#audit_axioms GroupApproximation.manuscriptProperIsometryStrictOrder

/-! ## L740 `0546c4f445c0` (definition) -/

#audit_axioms GroupApproximation.MaximalCStarProperCompression.StrictKazhdanCompression.proj
#audit_axioms GroupApproximation.MaximalCStarProperCompression.StrictKazhdanCompression.shift

/-! ## L740 `0d4f7970ddf4` (formalized) -/

#audit_axioms GroupApproximation.ProperProjectionCompression.star_isometry_mul_isometry
#audit_axioms GroupApproximation.ProperProjectionCompression.isometry_mul_star_isometry

/-! ## L740 `9b21786b2a7b` (formalized) -/

#audit_axioms GroupApproximation.MaximalCStarProperCompression.StrictKazhdanCompression.conjugate_mul_proj
#audit_axioms GroupApproximation.MaximalCStarProperCompression.StrictKazhdanCompression.proj_mul_conjugate

/-! ## L740 `f6355addf8b7` (formalized) -/

#audit_axioms GroupApproximation.ProperProjectionCompression.p_mul_q
#audit_axioms GroupApproximation.ProperProjectionCompression.q_mul_p
#audit_axioms GroupApproximation.ProperProjectionCompression.p_mul_star_u_mul_one_sub_q
#audit_axioms GroupApproximation.ProperProjectionCompression.isometry

/-! ## L740 `f67f0ad4466e` (formalized) -/

#audit_axioms GroupApproximation.MaximalCStarProperCompression.StrictKazhdanCompression.conjugate_ne_proj

/-! ## L756 `901f1b49e4e9` (formalized) -/

#audit_axioms GroupApproximation.ProperProjectionCompression.isometry_mul_star_ne_one
#audit_axioms GroupApproximation.ProperProjectionCompression.not_isStablyFiniteRing

/-! ## L756 `99f6411ca7a5` (formalized) -/

#audit_axioms GroupApproximation.ProperProjectionCompression.no_faithfulTracialState

/-! ## L756 `e4fcef4295ca` (formalized) -/

#audit_closed_axioms GroupApproximation.MatrixCoronaFinite.mfAlgebra_isStablyFinite
#audit_axioms GroupApproximation.ResiduallyFiniteDimensionalMF.isMFAlgebra

/-! ## L765 `07642b10d3ee` (formalized) -/

#audit_axioms GroupApproximation.AffineHNNBase.manuscriptSentence_ascendingHNNMatrixRealization
#audit_axioms GroupApproximation.AffineHNNBase.realization_injective
#audit_axioms GroupApproximation.AffineHNNBase.range_realization

/-! ## L765 `f979bf757c44` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.MaxInfiniteConverse.manuscriptMaxInfiniteConverseRemark

/-! ## L780 `330d435b12e2` (formalized) -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_reductionModuloOddRFAndMF
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.manuscriptSentence_reductionModuloOddSeparates
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.reductionHom
#audit_axioms GroupApproximation.Manuscript.NonMFSentences.dyadicReduceHom

/-! ## L780 `7d36ccc6e758` (formalized) -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.MaxInfiniteConverse.isOperatorMF
#audit_closed_axioms GroupApproximation.CliffordWitnessDirectDefect.manuscriptCliffordWitnessNotIsOperatorMF
