import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.ResidualCalculus
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness
import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalFactorization
import GroupApproximation.Manuscript.OneSidedMFRadical.PrescribedQuotients
import GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportAssembly
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedSectorProof
import GroupApproximation.Manuscript.OneSidedMFRadical.CompressionCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Leavitt.LeavittMatrixCompression
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedLeavittEquations
import GroupApproximation.Manuscript.OneSidedMFRadical.CountableNonMF
import GroupApproximation.Manuscript.OneSidedMFRadical.CanonicalSector
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRemarks
import GroupApproximation.Kazhdan.AmenableKazhdanFinite
import GroupApproximation.Kazhdan.KazhdanSeparableDescent

/-!
# Kernel audit for *One-sided Kazhdan transport and MF radicals*

Every numbered statement and every displayed equation of
`non_mf_groups_exist.tex` is printed here, and
`metadata/ONESIDED_TRANSPORT_LEDGER.md` has one row for each.
`scripts/check_onesided_transport_ledger.py` keeps the two in step in both
directions: a row may not name a declaration this file does not print, and
this file may not print a closed endpoint the ledger does not list.

`#audit_closed_axioms` does two things.  It fails the build if the axiom
closure of the proof contains anything beyond `propext`, `Classical.choice`
and `Quot.sound`, and it rejects any declaration whose type begins with a
caller-supplied binder.  The second half is what matters for an existence
headline: it is the machine check that a theorem is not quietly carrying
`(hSimple : IsSimpleGroup H)` or `(hConfiguration : ...)` as an
innocuous-looking manuscript parameter.  The manuscript's own quantifiers
therefore live inside named propositions -- `OneSidedCompressionCriterion`,
`PrescribedMFQuotients`, `PropositionDefect`, ... -- where the binder check is
supposed to find them, and not in front.

Two groups of declarations are printed with the weaker `#audit_axioms`,
which reports the closure without the binder check:

* the **printed definitions and the lemmas over arbitrary data** -- the
  compression-centralizer defect, the compression `Psi`, the corner
  conjugation, the amalgam.  These take the manuscript's own data (a group, a
  Leavitt family, a homomorphism) as leading binders, so they cannot have an
  empty telescope; they assume nothing, and each is consumed by a closed
  endpoint above.
* the **implementation lemmas** the closed endpoints are assembled from,
  audited at their own statements so that the manuscript rows are not the only
  place their closure is checked.
-/

/-! ## Section 1: the MF radical, the defect, and the three theorems -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculusLiteral
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculus
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptLiteralMFClosureIsQuotientPullback
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFRadicalIsLiteralClosureOfTrivial
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCoronaDenominator
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFUnitaryModels
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCoronaImagesAndTargets

-- Theorem A, printed as one theorem with four clauses, and its two exact
-- constituents.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompleteOneSidedCompressionCriterion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFiniteDimensionalSterility

-- The sterility paragraph.  The amenable case is not claimed: only the
-- group-theoretic half, `L` finite, is proved.  See the ledger.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectSterility

-- Theorem B.  The displayed conclusion and the structural clauses are closed;
-- the printed adjective "simple" is not, and is audited below.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.leavittFamily
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.rankTwelve_actualCoronaMFResidual_eq_top
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.closedStructuralProfile
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittFullRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCountableNonMFGroupExists
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNotEveryCountableGroupIsMF
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCountableNonOperatorMFGroupExists
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCountableKazhdanFullMFRadicalGroupExists
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSaturatedDefectKillsMFTargets

-- `eq:basic-defect`: the introduction's display of Corollary `cor:defect-hs`.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible

-- Theorem C.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedMFQuotients

/-! ## Section 2: one-sided compression in finite dimension -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFiniteDimensionalCommutantRigidity
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCommutantFiniteDimensionalHypothesisIsEssential
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedAmenableCaseChain
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSoficityIsNotObstructedByFullRadicals
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalsDoNotEntailNonsoficity
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntersectionOfKernelsIsNormal

/-! ## Section 3: Kazhdan transport in normalized Hilbert--Schmidt norm -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsIntersectionOfHSKernels
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsNormal
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormMatrixCoronaStableFinite
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanProjectionOrder
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarKazhdanProjectionOrder
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransport
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportPackage
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionGroupKazhdanTransport
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportAnyAmbient

/-! ## Section 4: the canonical Kazhdan sector and the MF radical -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCentralCoronaCorner
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCornerCoronaClass
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedNormalKazhdanCornerSteps
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectShadowInclusion
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectNormalKazhdanRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptDefectSaturation

/-! ## Section 5: the binary Leavitt self-compression -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.q_ne_zero
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tauUnit_eq_six_elementary
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL_mem
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.corner_hasKazhdanPropertyT
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedDefectConfiguration
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedLeavittAlgebraEquations
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCompressorEquations
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSectionFiveEquations

-- Property `(T)` at every representation universe.  The first two are general
-- transport results over caller-supplied data; the final profile is
-- hypothesis-free but universe-polymorphic rather than a closed `Prop`
-- package.  The ordinary audits are therefore intentional.
#audit_axioms GroupApproximation.hasKazhdanPropertyT_type0_iff
#audit_axioms GroupApproximation.HasKazhdanPropertyT.ofType0Model
#audit_axioms GroupApproximation.rankTwelve_propertyT_universe_profile

/-! ## Section 6: the full MF radical -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionDefect
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_conj_c

/-! ## Section 7: prescribed MF quotients -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSplitPrescribedProjection
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptUniversalFactorization
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedQuotientRelationCalculus
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.manuscriptMFClosurePullbackAlongFactorization

/-! ## Simplicity and the complete headline -/

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionSimple
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittHeadline

/-! ## Printed definitions and statements over arbitrary manuscript data

These carry no assumption.  Their types begin with the group, the ring, the
Leavitt family or the homomorphism that the manuscript itself quantifies over,
which is why the closed macro cannot accept them. -/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.map_printedDefect_to_range_le
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression
#audit_axioms GroupApproximation.RankTwelve.tau_fullCorner_tauInv
#audit_axioms GroupApproximation.MFCamouflage.Camouflage
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.literalMFClosure_eq_comap_of_factors
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.isCDEOperatorMF_quotient_iff_of_factors
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.camouflage_literalMFClosure_eq_comap
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.camouflage_isCDEOperatorMF_quotient_iff

/-! ## Implementation lemmas

Audited at their own statements, so that the manuscript rows above are not the
only place their axiom closure is checked. -/

-- The printed defect: its generating set, its generators, and the containment
-- in the development's larger compressor-group defect.
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefectSet
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect_generator_mem
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect_le_compressionCentralizerDefect

-- The ordinary-limit `K_2(V)` and the printed MF closure.
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.hsKernel
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.literalMFClosure
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.FactorsMFTargets
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.factorsMFTargets_iff_ker_le
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.manuscriptCoronaMFResidual_eq_comap_of_factors
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.factorsMFTargets_projection
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.camouflage_manuscriptCoronaMFResidual_eq_comap

-- `eq:pq`: the two Leavitt relations behind `q ≠ 0`.
#audit_axioms GroupApproximation.LeavittFamily.p0_add_p1
#audit_axioms GroupApproximation.LeavittFamily.t1_mul_p1_mul_s1

-- The ring-side centre computation used by the manuscript's simplicity proof.
-- These theorems quantify over a field or a unit, so they are support audits,
-- not zero-input manuscript endpoints.
#audit_axioms GroupApproximation.BinaryLeavitt.center_eq_bot
#audit_axioms GroupApproximation.BinaryLeavitt.central_units_trivial

-- Generic root extraction support.  The dense-entry theorem and exhaustive
-- Leavitt-family case split close the branch that was formerly missing.
#audit_axioms GroupApproximation.exists_elGen_mem_of_conjSingle_eq
#audit_axioms GroupApproximation.exists_elGen_mem_of_inv_entry_zero
#audit_axioms GroupApproximation.exists_elGen_mem_of_dense_entries
#audit_axioms GroupApproximation.exists_noncommuting_single_of_not_central
#audit_axioms GroupApproximation.rootDetection_of_leavittFamily

-- The two congruence-level endpoints, the full-linear-group centre
-- computation, and the exact reduction of simplicity to Preusser's sandwich.
-- The final theorem retains that sandwich as a visible leading hypothesis.
#audit_axioms GroupApproximation.relativeElementary_top
#audit_axioms GroupApproximation.congruenceSubgroup_bot
#audit_axioms GroupApproximation.center_eq_bot_of_central_units_trivial
#audit_axioms GroupApproximation.isSimpleGroup_of_preusser_sandwich

-- `eq:matrix-compression`: unitality, multiplicativity, the recovery identity
-- that gives injectivity, and the elementary-matrix formula.
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_one
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_mul
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_recover
#audit_axioms GroupApproximation.LeavittFamily.matrixCompressionHom_injective
#audit_axioms GroupApproximation.LeavittFamily.matrixCompression_elementaryUnit

-- `X`, `Y`, `XY = YX = I`, the nested `tau`, the Whitehead factorization and
-- the corner conjugation, over an arbitrary Leavitt family.
#audit_axioms GroupApproximation.RankTwelve.shift
#audit_axioms GroupApproximation.RankTwelve.shiftInv
#audit_axioms GroupApproximation.RankTwelve.shift_mul_shiftInv
#audit_axioms GroupApproximation.RankTwelve.shiftInv_mul_shift
#audit_axioms GroupApproximation.RankTwelve.tau
#audit_axioms GroupApproximation.RankTwelve.tau_eq_whitehead_product
#audit_axioms GroupApproximation.RankTwelve.shift_halfCorner_shiftInv

-- The concrete rank-twelve configuration behind `prop:defect`.
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_conj_corner_elementaryRoot
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_compresses_corner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.c_commutes_corner
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_c_commutator_ell
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.defect_ne_one
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.normalClosure_defect_eq_top

-- The amalgam of Section 7.
#audit_axioms GroupApproximation.MFCamouflage.projection
#audit_axioms GroupApproximation.MFCamouflage.blackHole_injective
#audit_axioms GroupApproximation.MFCamouflage.productVertex_injective
#audit_axioms GroupApproximation.MFCamouflage.defect_ne_one

/-! ## Rows added by the consolidation pass -/

-- Section 4, on the printed defect and the printed natural-dimension radical.
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanPrintedRadical
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanCoronaVanishing
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCriterionAssembly
#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectCoronaVanishing

-- The Introduction's amenable clause.  `finite_of_isAmenable_of_kazhdan` proves
-- the Bekka--de la Harpe--Valette step the manuscript cites, so this row carries
-- no literature dependence.
#audit_closed_axioms GroupApproximation.manuscriptAmenableKazhdanSterility
