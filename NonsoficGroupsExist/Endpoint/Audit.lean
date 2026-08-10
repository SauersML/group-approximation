import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Endpoint.ManuscriptStatements
import NonsoficGroupsExist.Sofic.SoficSequential
import NonsoficGroupsExist.Sofic.FreeLampReduction
import NonsoficGroupsExist.Sofic.WeakMFTransfer
import NonsoficGroupsExist.Sofic.WeakMFNonsoficDouble
import NonsoficGroupsExist.Sofic.SymmetricDoubleFlip
import NonsoficGroupsExist.Sofic.LineDouble
import NonsoficGroupsExist.Sofic.DoubleSoficTransfer
import NonsoficGroupsExist.Sofic.CentralCoverInheritance
import NonsoficGroupsExist.KOne.ClassicalKOne
import NonsoficGroupsExist.KOne.FactorizationCertificate
import NonsoficGroupsExist.Sofic.FinitelyPresentedLEF
import NonsoficGroupsExist.Leavitt.UnitsGLProfile
import NonsoficGroupsExist.KOne.AllRanksElementary
import NonsoficGroupsExist.Sofic.SoficPositiveControl
import NonsoficGroupsExist.Sofic.ExteriorMFProfile
import NonsoficGroupsExist.Sofic.HyperlinearNonScalar
import NonsoficGroupsExist.Sofic.HyperlinearReduction
import NonsoficGroupsExist.Sofic.HyperlinearUltraproduct
import NonsoficGroupsExist.Sofic.PhasePropagation
import NonsoficGroupsExist.Kun.KunDecomposition
import NonsoficGroupsExist.KunThom.KunThomTheorem
import NonsoficGroupsExist.PropertyT.FreeElementaryPropertyT
import NonsoficGroupsExist.Kazhdan.KazhdanComplex
import NonsoficGroupsExist.Kazhdan.KazhdanUniverse
import NonsoficGroupsExist.KOne.RefineLoopDischarge
import NonsoficGroupsExist.Kazhdan.ShalomFinitePresentation
import NonsoficGroupsExist.Covers.KazhdanCover
import NonsoficGroupsExist.Leavitt.FamilyRankFour
import NonsoficGroupsExist.Leavitt.StrictCentralCoverWitness
import NonsoficGroupsExist.Leavitt.IntegralGeneration
import NonsoficGroupsExist.Leavitt.RawSwapCompressors
import NonsoficGroupsExist.Leavitt.SelfSimilarityAlgebra
import NonsoficGroupsExist.Leavitt.PlaneEmbedding
import NonsoficGroupsExist.Leavitt.GeneralRankWords
import NonsoficGroupsExist.Leavitt.GeneralScheme
import NonsoficGroupsExist.Leavitt.GeneralCornerTheorem
import NonsoficGroupsExist.Sofic.Normalization
import NonsoficGroupsExist.Leavitt.FamilyVEmbedding
import NonsoficGroupsExist.Sofic.FreeGroupResiduallyFinite
import NonsoficGroupsExist.Endpoint.QuotientNonclosure
import NonsoficGroupsExist.Steinberg.Basic
import NonsoficGroupsExist.Steinberg.Perfect
import NonsoficGroupsExist.Steinberg.FinitelyGenerated
import NonsoficGroupsExist.Steinberg.A2System
import NonsoficGroupsExist.Steinberg.A2Kazhdan
import NonsoficGroupsExist.Steinberg.BinaryLeavitt
import NonsoficGroupsExist.Steinberg.FiniteControl
import NonsoficGroupsExist.Steinberg.KervaireSteinberg
import NonsoficGroupsExist.Steinberg.RootFiltration
import NonsoficGroupsExist.Steinberg.RootActions
import NonsoficGroupsExist.Steinberg.RootPlane
import NonsoficGroupsExist.Steinberg.RootPlaneFourier
import NonsoficGroupsExist.Steinberg.RootCharacterValuationBase
import NonsoficGroupsExist.Steinberg.RootCharacterValuation
import NonsoficGroupsExist.Steinberg.FreePropertyT
import NonsoficGroupsExist.Steinberg.Functoriality
import NonsoficGroupsExist.Steinberg.FiniteTypePropertyT

/-!
# Human-readable axiom report

This module pins the axiom reports for the public results and the three most
load-bearing mathematical inputs.  It is imported by the library root, so a
normal `lake build` prints these reports.  The stricter executable gate in
`scripts/Audit.lean` independently traverses the transitive axiom closure of
the entire project namespace and fails on anything beyond classical Lean.
-/

#print axioms NonsoficGroupsExist.nonsofic_groups_exist
#print axioms NonsoficGroupsExist.countable_nonsofic_groups_exist
#print axioms NonsoficGroupsExist.isSofic_iff_admitsEssentiallyFreeNearAction
#print axioms NonsoficGroupsExist.universalLeavittEL4_not_admitsEssentiallyFreeNearAction
#print axioms NonsoficGroupsExist.countable_group_without_essentiallyFreeNearAction_exists
#print axioms NonsoficGroupsExist.universalLeavittEL4_not_isSofic
#print axioms NonsoficGroupsExist.universalLeavittEL3_not_isSofic
#print axioms NonsoficGroupsExist.universalLeavittUnits_not_isSofic
#print axioms NonsoficGroupsExist.universalLeavittGL_not_isSofic
#print axioms NonsoficGroupsExist.ambient_profile
#print axioms NonsoficGroupsExist.ambient_full_profile
#print axioms NonsoficGroupsExist.universalLeavitt_profile
#print axioms NonsoficGroupsExist.binaryLeavitt_finiteField_profile
#print axioms NonsoficGroupsExist.exists_finitelyPresented_nonsofic_group
#print axioms NonsoficGroupsExist.exists_infinite_finitelyPresented_nonsofic_ambient_cover
#print axioms NonsoficGroupsExist.KunDecomposition.exists_expanderDecomposition
#print axioms NonsoficGroupsExist.KunSelectiveRepairExpansion.refined_bad_component_expands_at_every_positive_constant
#print axioms NonsoficGroupsExist.KunThomTheorem.isLEF_of_exactProductExpansion
#print axioms NonsoficGroupsExist.commute_of_perfect_quotient
#print axioms NonsoficGroupsExist.subgroup_eq_top_of_surjects_mod_central
#print axioms NonsoficGroupsExist.CentralExtension.lift_centralizes_perfect_preimage
#print axioms NonsoficGroupsExist.SteinbergGroup.projection_surjective
#print axioms NonsoficGroupsExist.SteinbergGroup.centralExtension
#print axioms NonsoficGroupsExist.SteinbergGroup.fin_isPerfect
#print axioms NonsoficGroupsExist.SteinbergGroup.finitelyGenerated
#print axioms NonsoficGroupsExist.SteinbergGroup.x_injective
#print axioms NonsoficGroupsExist.SteinbergGroup.a2System
#print axioms NonsoficGroupsExist.SteinbergGroup.binaryLeavitt_exists_rootSet_isKazhdan
#print axioms NonsoficGroupsExist.KervaireSteinberg.commutator_commutes_of_commutators_mem_center
#print axioms NonsoficGroupsExist.KervaireSteinberg.commutator_eq_of_eq_mod_center
#print axioms NonsoficGroupsExist.KervaireSteinberg.commutator_eq_of_same_projection
#print axioms NonsoficGroupsExist.KervaireSteinberg.commutator_commutator_eq
#print axioms NonsoficGroupsExist.KervaireSteinberg.lifts_commute_of_spare_index
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_lifts_commute
#print axioms NonsoficGroupsExist.KervaireSteinberg.projection_correctedRoot
#print axioms NonsoficGroupsExist.KervaireSteinberg.correctedRoot_eq_commutator_of_lifts
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_correctedRoot_eq_of_middle_ne
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_correctedRoot_eq
#print axioms NonsoficGroupsExist.KervaireSteinberg.projection_canonicalRoot
#print axioms NonsoficGroupsExist.KervaireSteinberg.canonicalRoot_eq_correctedRoot
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_canonicalRoot_commute
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_canonicalRoot_commutator
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_correctedRoot_mul
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_canonicalRoot_mul
#print axioms NonsoficGroupsExist.KervaireSteinberg.splittingHom_isSection
#print axioms NonsoficGroupsExist.KervaireSteinberg.every_centralExtension_splits
#print axioms NonsoficGroupsExist.KervaireSteinberg.correctedRoot_zero
#print axioms NonsoficGroupsExist.KervaireSteinberg.fin_correctedRoot_commute
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.projection_surjective
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.isPerfect
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.finitelyGenerated
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.elementaryBase_not_isSofic
#print axioms NonsoficGroupsExist.LeavittStrictCentralCoverWitness.witness_strict
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.everyCentralExtensionSplits
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.rankThree_hasKazhdanPropertyT
#print axioms NonsoficGroupsExist.BinaryLeavittSteinberg.hasKazhdanPropertyT
#print axioms NonsoficGroupsExist.FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT
#print axioms NonsoficGroupsExist.UniversalRankFour.witness_not_isLEF
#print axioms NonsoficGroupsExist.ThompsonFObstruction.finite_image_generatorCommutator_eq_one
#print axioms NonsoficGroupsExist.isSofic_of_finite
#print axioms NonsoficGroupsExist.isSofic_semidirectProduct_of_finite
#print axioms NonsoficGroupsExist.freeLampMulEquivSymmetricDoubleFlip
#print axioms NonsoficGroupsExist.doubleToLine_injective
#print axioms NonsoficGroupsExist.isSofic_freeLamp_flip_of_isSofic_lineDouble
#print axioms NonsoficGroupsExist.not_isSofic_lineDouble_of_not_isSofic_freeLamp_flip
#print axioms NonsoficGroupsExist.isSofic_multiplicative_int
#print axioms NonsoficGroupsExist.isSofic_iff_productRestricted
#print axioms NonsoficGroupsExist.isSofic_of_soficApproximation
#print axioms NonsoficGroupsExist.isSofic_iff_nonempty_soficApproximation
#print axioms NonsoficGroupsExist.isLEF_of_finite
#print axioms NonsoficGroupsExist.isLEF_multiplicative_int
#print axioms NonsoficGroupsExist.isLEF_iff_textbook
#print axioms NonsoficGroupsExist.isKazhdanPair_iff_complex
#print axioms NonsoficGroupsExist.hasKazhdanPropertyT_iff_complex
#print axioms NonsoficGroupsExist.IsKazhdanPair.liftUniverse
#print axioms NonsoficGroupsExist.HasKazhdanPropertyT.liftUniverse
#print axioms NonsoficGroupsExist.IsKazhdanPair.lowerUniverse
#print axioms NonsoficGroupsExist.hasKazhdanPropertyT_universe_iff
#print axioms NonsoficGroupsExist.hasKazhdanPropertyT_iff_textbook

-- The unconditional K₁-vanishing chain (session 54): narrow reduction,
-- scalar reduction, checkpoint B4, GL = EL, and the Whitehead-form
-- headline.  All must report only the three standard axioms.
#print axioms NonsoficGroupsExist.BinaryLeavitt.narrowReduction_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.scalarReduction_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.stableUnits_eq_top_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.glTwo_eq_elementary_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.glFour_eq_elementary_holds

-- The exact manuscript endpoints: one declaration per printed headline
-- statement, so the report records what each printed theorem rests on.
#print axioms NonsoficGroupsExist.Manuscript.theoremA_exact
#print axioms NonsoficGroupsExist.Manuscript.theoremB_exact
#print axioms NonsoficGroupsExist.Manuscript.theoremC_exact
#print axioms NonsoficGroupsExist.Manuscript.theoremC_covers_theoremB_groups
#print axioms NonsoficGroupsExist.Manuscript.theoremD_subgroups
#print axioms NonsoficGroupsExist.Manuscript.cor_fgring_printed
#print axioms NonsoficGroupsExist.Manuscript.cor_fgring_exact
#print axioms NonsoficGroupsExist.Manuscript.cor_fgring_countableFree
#print axioms NonsoficGroupsExist.binaryLeavittWhiteheadK1_subsingleton
#print axioms NonsoficGroupsExist.binaryLeavittElementaryColim_eq_top
#print axioms NonsoficGroupsExist.binaryLeavittClassicalK1_subsingleton
#print axioms NonsoficGroupsExist.BinaryLeavitt.exists_elementaryCertificate
#print axioms NonsoficGroupsExist.BinaryLeavitt.exists_moveList
#print axioms NonsoficGroupsExist.BinaryLeavitt.Move.eval_mem_stableUnits
#print axioms NonsoficGroupsExist.BinaryLeavitt.K1_trivial

-- The unit-group and general-linear profiles (Theorem B(i) closed): finite
-- generation, infinitude, property (T), and nonsoficity of `L_k(1,2)ˣ` and
-- of every positive-rank `GL_r` over every finite field.
#print axioms NonsoficGroupsExist.binaryLeavittUnits_profile
#print axioms NonsoficGroupsExist.binaryLeavittGL_profile

-- Theorem C's Kazhdan half, proved internally and included explicitly in the
-- public axiom report.
#print axioms NonsoficGroupsExist.Shalom.exists_presented_kazhdan_cover
#print axioms NonsoficGroupsExist.Shalom.exists_finitelyPresented_kazhdan_cover
#print axioms NonsoficGroupsExist.exists_kazhdan_finitelyPresented_cover_of_not_isSofic

-- All-ranks collapse, perfectness, and the rank-two compression over
-- `L_k(1,2)`: `GL_n = EL_n` for every `n ≥ 2` over every field, the unit
-- group is perfect, and the two-by-two Leavitt-corner theorem closes over
-- every finite field.
#print axioms NonsoficGroupsExist.BinaryLeavitt.elementaryGroup_eq_top
#print axioms NonsoficGroupsExist.BinaryLeavitt.glAll_eq_elementary
#print axioms NonsoficGroupsExist.BinaryLeavitt.binaryLeavittUnits_perfect
#print axioms NonsoficGroupsExist.binaryLeavittRankTwo_not_isSofic

-- The coefficient ring in the explicit Steinberg endpoint has an absolute
-- associative-ring presentation: four generators, the five Leavitt
-- equations, and the characteristic-two equation.  The equivalence is
-- constructed in both directions rather than assumed.
#print axioms NonsoficGroupsExist.BinaryLeavittAbsolute.ringEquiv

-- `lem:fplef`, closed: finitely presented LEF groups are residually finite.
#print axioms NonsoficGroupsExist.finitelyPresented_isLEF_residuallyFinite

-- `cor:fgring` at the generality the corollary is stated in: any nontrivial
-- countable finite-type algebra over a finite field carrying a binary Leavitt
-- family.  The manuscript's margin note names these, so an ordinary build
-- reports their axioms rather than leaving them to the whole-namespace scan.
#print axioms NonsoficGroupsExist.FamilyRankFour.ambient_not_isSofic
#print axioms NonsoficGroupsExist.FamilyRankFour.elementary_not_isSofic
#print axioms NonsoficGroupsExist.FamilyRankFour.units_not_isSofic
#print axioms NonsoficGroupsExist.FamilyRankFour.gl_not_isSofic

-- `thm:corner` at every adjacent pair `(m, m + 1)` with `m ≥ 2`, at the
-- printed hypotheses, and its characteristic-two discharge of the
-- membership hypothesis (ii).
#print axioms NonsoficGroupsExist.GeneralCornerTheorem.corner_not_isSofic
#print axioms NonsoficGroupsExist.GeneralCornerTheorem.corner_not_isSofic_of_charTwo

-- `lem:normalization`: the inverse-compatible normalization of a sofic
-- approximation is constructed, not just estimated.
#print axioms NonsoficGroupsExist.SoficApproximation.exists_normalization

-- `prop:vembed`: Thompson's `V` embeds into the unit group of any
-- nontrivial ring carrying a binary Leavitt family, with `eq:Ug` on tables.
#print axioms NonsoficGroupsExist.LeavittFamily.vEmbeddingOfFamily_injective
#print axioms NonsoficGroupsExist.LeavittFamily.vEmbeddingOfFamily_tableEquiv

-- `rem:quotients`: free groups are residually finite, and none of the
-- classes of sofic, LEF, or residually finite groups is closed under
-- quotients.
#print axioms NonsoficGroupsExist.freeGroup_residuallyFinite
#print axioms NonsoficGroupsExist.isSofic_freeGroup
#print axioms NonsoficGroupsExist.exists_sofic_group_with_nonsofic_quotient
#print axioms NonsoficGroupsExist.exists_isLEF_group_with_non_isLEF_quotient
#print axioms NonsoficGroupsExist.exists_residuallyFinite_group_with_non_residuallyFinite_quotient

-- Internally proved operator-norm MF transfer mechanisms.
#print axioms NonsoficGroupsExist.isWeakMF_of_injective
#print axioms NonsoficGroupsExist.isWeakMF_of_residuallyFinite
