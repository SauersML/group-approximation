#!/usr/bin/env python3
r"""Regenerate the numbered-claim manifest for the non-MF manuscript.

The independent maps below are the reviewed boundary between the current
printed claims and their proofs.  An exact claim names one current Lean
declaration that states the whole proposition.  A paper-proved claim records
the external inputs consumed by the complete proof printed in the manuscript.
The generator also records every additional exact badge printed in the same
environment, so a multi-conclusion statement cannot hide an unreviewed badge.

Each manuscript has its own maps: `non_mf_groups_exist.tex` uses the
unprefixed maps and `non_mf_group_notes.tex` the `NOTES_` maps.  The notes also
record literature-input claims, whose stated input is not formalized.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path

from check_non_mf_claim_manifest import read_printed_claims


REPO = Path(__file__).resolve().parent.parent


# One declaration stating the complete printed proposition.  This map is
# independent of the badges in the TeX: generation fails unless the reviewed
# declaration is also printed in the environment.
EXACT_TARGETS: dict[str, tuple[str, str]] = {
    "prop:mf-residual-calculus": (
        "Manuscript/OneSidedMFRadical/PrintedDefinitions",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "allMFTargetsKill_iff_allCoronasKill"),
    "thm:compression-criterion": (
        "Manuscript/OneSidedMFRadical/PrintedCriterion",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptOneSidedCompressionCriterion"),
    "thm:headline": (
        "Manuscript/OneSidedMFRadical/UnitGroupHeadline",
        "GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline."
        "manuscriptUnitGroupHeadline"),
    "lem:stable-finite": (
        "Manuscript/OneSidedMFRadical/StableFiniteness",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptNormMatrixCoronaStableFinite"),
    "lem:kazhdan-projection-order": (
        "Manuscript/OneSidedMFRadical/KazhdanProjectionOrderLiteral",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptLiteralMaximalCStarKazhdanProjectionOrder"),
    "thm:transport": (
        "Manuscript/OneSidedMFRadical/TransportPrintedRoute",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "TransportPrintedRoute.manuscriptPrintedTransportHS"),
    "cor:defect-hs": (
        "Manuscript/OneSidedMFRadical/DefectHS",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptCompressionDefectHSInvisible"),
    "lem:central-corona-corner": (
        "Manuscript/OneSidedMFRadical/CentralCoronaCornerPrintedRoute",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "CentralCoronaCornerPrintedRoute.manuscriptPrintedCentralCoronaCorner"),
    "thm:normal-kazhdan": (
        "Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "NormalKazhdanPrintedRoute.manuscriptNormalKazhdanRadical_printedRoute"),
    "prop:max-infinite": (
        "Analysis/StrictCompressionFromPrinted",
        "GroupApproximation.MaximalCStarPrintedHypotheses."
        "manuscriptMaximalCStarRemarkFromPrintedHypotheses"),
    "thm:factorization-nonmf-trace": (
        "Manuscript/NinetyNineProblems/ProblemXGroups",
        "GroupApproximation.NinetyNineProblems."
        "canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF"),
    "prop:locally-rf-by-z-trace": (
        "Analysis/AmenableExtensionAmenableTrace",
        "GroupApproximation.AmenableExtensionTrace."
        "manuscriptPrintedAmenableExtensionTrace"),
    "prop:clifford-self-embedding": (
        "Sofic/CliffordWitnessDirectDefect",
        "GroupApproximation.CliffordWitnessDirectDefect."
        "manuscriptMapSignEqOneOfIsOperatorMFTarget"),
    "thm:full-defect-ring": (
        "Manuscript/OneSidedMFRadical/FullDefectRingEJZUnconditional",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "FullDefectRingEJZUnconditional."
        "manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics"),
    "cor:simple-infinite-ring": (
        "Manuscript/OneSidedMFRadical/FullDefectRingEJZUnconditional",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "FullDefectRingEJZUnconditional."
        "manuscriptSimpleInfiniteRingRankTwoAllCharacteristics"),
    "cor:one-sided-ring-maximal": (
        "Manuscript/OneSidedMFRadical/FullDefectRingEJZUnconditional",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "FullDefectRingEJZUnconditional."
        "manuscriptOneSidedRingMaximalIsometryAllCharacteristics"),
    "lem:two-copies": (
        "Manuscript/OneSidedMFRadical/RankDescentPrintedLemmas",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted."
        "manuscriptTwoCopiesLemma"),
    "lem:rank-two": (
        "Manuscript/OneSidedMFRadical/RankDescentPrintedLemmas",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted."
        "manuscriptRankTwoNormalGeneration"),
    # `thm:amenable-trace` retargeted 2026-09-17 to the countable form (W and
    # W_0 countable, not MF both as IsOperatorMF and IsCDEOperatorMF).
    "thm:amenable-trace": (
        "Manuscript/NonMF/Full/AmenableCountable/TraceCountable",
        "GroupApproximation.Full.NM08."
        "manuscriptAmenableNonquasidiagonalTraceCountable"),
    "prop:clifford-locally-rf": (
        "Sofic/CliffordWitnessSoficPrinted",
        "GroupApproximation.AmenableTraceTheorem.manuscriptCliffordLocallyRF"),
    # `thm:mf-quotient-units` prints two badges: `manuscriptMFQuotientUnitsKOne`
    # (the universal-property/MF/radical=commutator conjunction, quantified at
    # R itself) and `manuscriptMFQuotientUnitsKOneAtBaseRing` (the "Equivalently"
    # radical=commutator/quotient=K_1(R) reformulation, quantified over every
    # n>=1).  Neither alone covers every clause at every printed n, so this is
    # collective; see COLLECTIVE_CLAIMS.
    "thm:mf-quotient-units": (
        "Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof",
        "GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne"),
    # `lem:ring-compression-cell` moved to EXACT_TARGETS 2026-09-09: badge
    # landed (commit b9ee08b1d, module on origin at b46935710).
    "lem:ring-compression-cell": (
        "Manuscript/OneSidedMFRadical/RankFourCompressionCellPrinted",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "RankFourCompressionCellPrinted.manuscriptRankFourCompressionCell"),
    # The torsion-defect proposition, the Leavitt corollary and the seven
    # chain-core environments moved to EXACT_TARGETS 2026-09-17: each now
    # prints a closed declaration stating the whole environment.
    "prop:torsion-defect-ring": (
        "Manuscript/OneSidedMFRadical/TorsionComplementaryIdempotents",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "TorsionComplementaryIdempotents."
        "manuscriptTorsionComplementaryIdempotents"),
    "cor:leavitt-mf-quotient": (
        "Manuscript/NonMFSentences/LeavittKOneFormulaSentences",
        "GroupApproximation.LeavittKOneFormulaSentences."
        "manuscriptLeavittMFQuotientFull"),
    "lem:chain-core-models": (
        "Manuscript/NonMF/Full/ChainCoreModels/PrintedLemma",
        "GroupApproximation.Full.NM12.printedChainCoreModels_closed"),
    "lem:transient-matrices": (
        "Manuscript/NonMFSentences/TransientMatricesClosed",
        "GroupApproximation.Manuscript.NonMFSentences.TransientMatrices."
        "printedTransientMatrices_closed"),
    "thm:core-ring-reflection": (
        "Manuscript/NonMFSentences/ChainCoreClosures",
        "GroupApproximation.ChainCore.ChainCoreClosures."
        "printedCoreRingReflection_closed"),
    "prop:bilateral-three": (
        "Manuscript/NonMFSentences/ChainCoreClosures",
        "GroupApproximation.ChainCore.ChainCoreClosures."
        "printedBilateralThree_closed"),
    "thm:core-mf-radical": (
        "Manuscript/NonMFSentences/ChainCoreClosures",
        "GroupApproximation.ChainCore.ChainCoreClosures."
        "printedCoreMFRadical_closed"),
    "lem:involution-localization": (
        "Dynamics/TransientCellsClosed",
        "GroupApproximation.ClopenCrossedProduct."
        "printedInvolutionLocalization_closed"),
    "cor:dynamic-rank-budget": (
        "Manuscript/NonMFSentences/ChainCoreClosures",
        "GroupApproximation.ChainCore.ChainCoreClosures."
        "printedDynamicRankBudget_closed"),
}


# These environments deliberately carry no Lean badge.  Their proofs
# are complete in the manuscript.  The tuple lists precisely the outside
# mathematical results used by that proof; an empty tuple means there is no
# additional external input beyond the listed manuscript dependencies.
PAPER_PROOFS: dict[str, tuple[str, ...]] = {
    # `lem:block-structure`, `thm:finite-algebra-transport`,
    # `thm:perfect-block-radical`, `thm:fp-sofic-radical`,
    # `prop:cyclic-hnn-absorption`, `thm:sofic-cyclic-mf` and
    # `cor:relative-quotient` were cut as printed environments in the
    # 2026-09-08 rewrite (no `\label` for any of them remains in the tex);
    # their PAPER_PROOFS/DEPENDENCIES entries were dropped 2026-09-09 to
    # match.  Their Lean declarations, where any existed, are simply no
    # longer cited by the manuscript.
    #
    # `thm:amenable-trace` and `prop:clifford-locally-rf` were themselves
    # cut on 2026-09-08 (their content folded into `thm:fp-sofic-radical`)
    # but are BACK as printed environments as of 2026-09-09, each with its
    # own single exact badge; both moved to EXACT_TARGETS.
    # `prop:torsion-defect-ring` is a new printed proposition as of
    # 2026-09-09 (the torsion-defect complement to `thm:full-defect-ring`);
    # it was a paper-proof claim until 2026-09-17, when it and the
    # dynamical core results moved to EXACT_TARGETS (see the note there).
    # `thm:full-defect-ring` moved to EXACT_TARGETS 2026-09-07:
    # `PropertyT/IntegralColumnPlaneClosure.lean` closed
    # `FinitelyGeneratedRingGeneralRankElementaryPropertyT` unconditionally
    # (commit 343a1c4a4), and `FullDefectRingEJZUnconditional.lean` spends it,
    # so the corollaries below no longer carry any external input either --
    # both proofs just say "Theorem thm:full-defect-ring applies", which is
    # now unconditional.  `cor:simple-infinite-ring` and
    # `cor:one-sided-ring-maximal` moved to EXACT_TARGETS the same day, once
    # badge batch 3 gave both hypothesis-free n>=2 carriers.
    # `cor:affine-clifford-trace` and `lem:commutator-in-defect` were
    # removed as separate numbered environments in the 2026-09-07 rewrite:
    # the trace corollary's content moved into `thm:amenable-trace`'s own
    # proof (which now derives everything from `prop:clifford-locally-rf`
    # directly), and the defect-containment step is now cited inline in
    # `thm:torsion-free`'s proof via `\eqref{eq:defect-functorial}` rather
    # than a separate lemma.  Their entries here and in DEPENDENCIES were
    # dropped to match; neither claim id is printed any more.
    "thm:hull": (
        "Hull, Theorem 7.1",),
    "lem:saturation": (
        "Osin, Lemma 7.1", "Hull, Theorem 3.12",
        "Hull, Corollary 5.7 and Lemma 5.8"),
    "thm:torsion-free": (
        "Fournier-Facio, Section 2", "Hull, Corollary 7.4"),
    # `prop:linear-collapse` moved to EXACT_TARGETS 2026-09-07 (badges
    # landed: QuantitativeCollapse.manuscriptLinearCollapse /
    # .manuscriptLinearCollapseConverse, one per direction -- collective).
    # `cor:relative-quotient` (was `("Hull, Corollary 7.4",)`) was cut as a
    # printed environment in the 2026-09-08 rewrite; see the note above
    # `lem:ring-compression-cell`.
    "cor:regular-nonmf-algebra": (
        "Osin, Theorem 1.2", "Dahmani--Guirardel--Osin, Theorem 2.35",
        "Gerasimova--Osin, Theorem 1.1"),
    # `lem:two-copies` and `lem:rank-two` are EXACT_TARGETS, not here (both
    # badged: RankDescentPrintedLemmas.manuscriptTwoCopiesLemma /
    # .manuscriptRankTwoNormalGeneration).
    # `thm:leavitt-mf-quotient` was replaced 2026-09-07 by the general
    # `thm:mf-quotient-units` plus the Leavitt-specific `cor:leavitt-mf-quotient`.
    # `thm:mf-quotient-units` moved to EXACT_TARGETS 2026-09-09: two badges
    # landed (MFQuotientUnitsKappaProof.manuscriptMFQuotientUnitsKOne and
    # MFQuotientCanonicalKOne.manuscriptMFQuotientUnitsKOneAtBaseRing), so the
    # AGP/Menal-Moncasi/Blackadar-Kirchberg inputs below are now internal to
    # those proofs rather than boundary citations.
}


# No single badge in these environments includes every printed clause.
# Their declarations are recorded as collective, with no claim that one
# declaration is a complete wrapper.
COLLECTIVE_CLAIMS: set[str] = {
    # Kernel equivalence and the faithful C-star/group embedding implication
    # are separate exact statements. Neither alone is all of Lemma 2.1.
    "prop:mf-residual-calculus",
    "prop:clifford-self-embedding",
    "thm:factorization-nonmf-trace",
    # `thm:full-defect-ring` prints two badges: the n>=2 rank-two descent
    # (manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics), and
    # the "group B" sentence (UniversalGroupSigma.manuscriptFullComplementary
    # IdempotentsUniversal: property (T), MF-triviality, finite generation,
    # normal generation by an involution, and the homomorphism to
    # EL_n(R) with normally generating image, for every n>=2).
    "thm:full-defect-ring",
    # `cor:simple-infinite-ring` prints one badge per sentence
    # (manuscriptSimpleInfiniteRingRankTwoAllCharacteristics /
    # manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics).
    "cor:simple-infinite-ring",
    # `cor:one-sided-ring-maximal` prints three badges as of 2026-09-09
    # (the separate n>=2 isometry clause was cut from the printed
    # statement): the n>=4 isometry clause, the n>=2 reduced-C*-algebra
    # clause, and the unit-group-not-MF clause; no single one is the whole
    # corollary.
    "cor:one-sided-ring-maximal",
    # `thm:mf-quotient-units` prints two badges as of 2026-09-09: see the
    # comment at its EXACT_TARGETS entry.
    "thm:mf-quotient-units",
}


# The paper-level dependency graph.  Every name is another live numbered
# claim, even when the dependent theorem is printed earlier for exposition.
DEPENDENCIES: dict[str, list[str]] = {
    "prop:mf-residual-calculus": [],
    "thm:compression-criterion": [
        "cor:defect-hs", "thm:normal-kazhdan", "prop:mf-residual-calculus"],
    "thm:full-defect-ring": [
        "thm:compression-criterion", "lem:two-copies", "lem:rank-two"],
    "thm:headline": [
        "thm:full-defect-ring", "cor:one-sided-ring-maximal"],
    "cor:simple-infinite-ring": ["thm:full-defect-ring"],
    "cor:one-sided-ring-maximal": [
        "thm:full-defect-ring", "prop:max-infinite"],
    "lem:stable-finite": [],
    "lem:kazhdan-projection-order": [],
    "thm:transport": ["lem:stable-finite", "lem:kazhdan-projection-order"],
    "cor:defect-hs": ["thm:transport"],
    "lem:central-corona-corner": [],
    "thm:normal-kazhdan": ["lem:central-corona-corner"],
    "lem:two-copies": [],
    "lem:rank-two": [],
    "thm:mf-quotient-units": ["thm:full-defect-ring"],
    "cor:leavitt-mf-quotient": ["thm:mf-quotient-units"],
    # The proper-isometry construction is now inside this proposition's
    # proof, not a separate numbered lemma in the manuscript.
    "prop:max-infinite": ["lem:kazhdan-projection-order"],
    "thm:factorization-nonmf-trace": [],
    "prop:locally-rf-by-z-trace": [],
    "prop:clifford-self-embedding": ["thm:compression-criterion"],
    "thm:hull": [],
    "lem:saturation": ["thm:hull"],
    "thm:torsion-free": [
        "thm:compression-criterion", "lem:saturation"],
    "lem:ring-compression-cell": [],
    "cor:regular-nonmf-algebra": ["thm:torsion-free"],
    "prop:torsion-defect-ring": [
        "thm:compression-criterion", "lem:ring-compression-cell"],
    "lem:chain-core-models": [],
    "lem:transient-matrices": ["lem:chain-core-models"],
    "thm:core-ring-reflection": [
        "lem:chain-core-models", "lem:transient-matrices"],
    "thm:core-mf-radical": [
        "prop:torsion-defect-ring", "lem:chain-core-models",
        "lem:transient-matrices", "prop:bilateral-three"],
    "prop:bilateral-three": [
        "thm:compression-criterion", "lem:chain-core-models",
        "lem:transient-matrices", "thm:core-ring-reflection"],
    "lem:involution-localization": [
        "lem:transient-matrices", "thm:core-mf-radical"],
    "cor:dynamic-rank-budget": [
        "prop:bilateral-three", "thm:core-mf-radical",
        "lem:involution-localization", "thm:core-ring-reflection",
        "prop:torsion-defect-ring"],
    "prop:clifford-locally-rf": [
        "prop:clifford-self-embedding", "prop:locally-rf-by-z-trace",
        "thm:factorization-nonmf-trace"],
    "thm:amenable-trace": ["prop:clifford-locally-rf"],
}


# One declaration stating the complete printed proposition of each exact
# environment of `non_mf_group_notes.tex`.  For a collective claim the entry
# is one of the printed clause declarations; see NOTES_COLLECTIVE_CLAIMS.
NOTES_EXACT_TARGETS: dict[str, tuple[str, str]] = {
    "def:E": (
        "Sofic/LiteralNonMFPresentation",
        "GroupApproximation.LiteralNonMFPresentation."
        "manuscriptLiteralPresentation"),
    "prop:literal-base-T": (
        "Sofic/LiteralBaseP13PropertyTBridge",
        "GroupApproximation.LiteralBaseP13PropertyTBridge."
        "manuscriptBaseHasKazhdanPropertyT"),
    "lem:linear": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptLinearModel"),
    "prop:witness": (
        "Sofic/LiteralNonMFLinearWitness",
        "GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one"),
    "cor:relator-uniform": (
        "Sofic/LiteralRelatorObstruction",
        "GroupApproximation.LiteralRelatorObstruction."
        "literal_relator_uniform_obstruction"),
    "thm:signfree": (
        "Sofic/LiteralSignFreeQuotient",
        "GroupApproximation.LiteralSignFreeQuotient."
        "signFreeQuotient_not_isCDEOperatorMF"),
    "thm:reduced": (
        "Sofic/LiteralNonMFEndpoint",
        "GroupApproximation.LiteralNonMFEndpoint.manuscriptTheoremD"),
    "thm:Esofic": (
        "Sofic/LiteralSoficAssembly",
        "GroupApproximation.LiteralSoficAssembly.markedGroup_isSofic"),
    "lem:mftrace-group": (
        "Sofic/TraceSeparationEndpoint",
        "GroupApproximation.manuscriptMFTraceGroupBridge"),
    "thm:trace": (
        "Sofic/TraceSeparationEndpoint",
        "GroupApproximation.manuscriptTraceSeparation"),
    "thm:transport-variants": (
        "Sofic/ManuscriptSubgroupSpecializations",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptWeightedTransportSubgroup"),
    "def:pattern": (
        "Sofic/ConjugationDatumAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptMarkedKazhdanPattern_anyUniverse"),
    "def:invisible": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptHSInvisibleCharacterization"),
    "thm:criterion": (
        "Sofic/FiniteNormalAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptFiniteNormalObstructionCriterion_anyUniverse"),
    "cor:marked-obstruction": (
        "Sofic/LiteralNonMFEndpoint",
        "GroupApproximation.LiteralNonMFEndpoint."
        "literal_mark_mem_manuscriptCoronaMFResidual"),
    "cor:generaltransport": (
        "Sofic/DefectActionAnyUniverse",
        "GroupApproximation.KazhdanAsymptoticCommutant."
        "compressionGroup_transport_both_anyUniverse"),
    "thm:compression-radical": (
        "Sofic/DefectRadicalAnyUniverse",
        "GroupApproximation.KazhdanAsymptoticCommutant."
        "manuscriptCompressionRadical_anyUniverse"),
    "thm:abstract-nk": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptAbstractNormalKazhdanObstruction"),
    "thm:normal-kazhdan": (
        "Sofic/NormalKazhdanAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptNormalKazhdanObstruction_anyUniverse"),
    "cor:intrinsic-nk": (
        "Sofic/NormalKazhdanAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptIntrinsicNormalKazhdanRadical_anyUniverse"),
    "thm:exactfd-intrinsic": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptTheoremB"),
    "cor:notRFD": (
        "Sofic/LiteralFiniteDimensionalObstruction",
        "GroupApproximation.LiteralFiniteDimensionalObstruction."
        "manuscriptFiniteDimensionalConsequences"),
    "thm:cyclic": (
        "Monsters/LiteralCyclicCalibration",
        "GroupApproximation.LiteralCyclicCalibration."
        "manuscriptCyclicCalibration"),
    "cor:scaling-family": (
        "Sofic/ScalingFamilyEndpoint",
        "GroupApproximation.ScalingFamilyEndpoint.manuscriptTheoremFamily"),
    "def:radical": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptMFRadical"),
    "lem:portable": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptRadicalPortability"),
    "prop:univquot": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptUniversalMFQuotient"),
    "cor:exactradical": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptExactRadicalFromCandidateQuotient"),
    "cor:pullback": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptRadicalReductionToQuotient"),
    "thm:fixed-radical-computer": (
        "Computability/MFRadicalComputer",
        "GroupApproximation.MFRadicalComputer.closed_package"),
    "cor:nofaithful": (
        "Sofic/LiteralNonMFConsequences",
        "GroupApproximation.LiteralNonMFConsequences."
        "literal_no_faithful_corona_subalgebra_target"),
    "lem:permanence": (
        "Sofic/OperatorMFPositiveControls",
        "GroupApproximation.IsOperatorMF.subgroup"),
    "cor:quotclosure": (
        "Sofic/LiteralMFQuotientControls",
        "GroupApproximation.LiteralMFQuotientControls."
        "manuscriptQuotientNonclosure"),
    "thm:projection-collapse": (
        "Sofic/ProjectionCompressionCollapse",
        "GroupApproximation.ProjectionCompressionCollapse."
        "corona_projection_collapse"),
    "def:invwitness": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptInvolutiveCollapsePattern"),
    "thm:collapse": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptInvolutiveCollapse"),
    "cor:collapsequot": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptCollapseRadicalReduction"),
    "thm:notes-spectral-motion": (
        "Manuscript/SpectralPaper/MainTheorems",
        "GroupApproximation.SpectralPaper.spectralCompressionTheorem"),
    "lem:faithfultrace": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptFaithfulTraceAndStableFiniteness"),
    "prop:blocknormalform": (
        "Sofic/LiteralBlockNormalForm",
        "GroupApproximation.LiteralBlockNormalForm.markedGroupEquivModel"),
    "lem:window": (
        "Sofic/BlockCliffordTowerSofic",
        "GroupApproximation.BlockCliffordTowerSofic."
        "manuscriptResiduallyFiniteWindow"),
    "prop:horn": (
        "Sofic/LiteralUniversalHorn",
        "GroupApproximation.LiteralUniversalHorn."
        "manuscriptLiteralUniversalHorn"),
    "thm:notes-abelian-boundary": (
        "Manuscript/NonMFNotes/Full/AbelianBoundary/Boundary",
        "GroupApproximation.Full.NN06.notesAbelianBoundary"),
    "cor:undecidable": (
        "Computability/BooneWordProblemUndecidable",
        "GroupApproximation.Computability.not_computablePred_wordProblemPred"),
}


# Environments of the notes with a complete proof in the manuscript and no
# in-environment badge, with the outside results that proof consumes.
NOTES_PAPER_PROOFS: dict[str, tuple[str, ...]] = {
    "thm:mf-radical-arithmetic": (
        "decidability of fixed-dimensional unitary feasibility over the real "
        "closed field",
    ),
    "thm:fixed-radical-membership": (
        "Kharlampovich's finitely presented solvable group with undecidable "
        "word problem",
    ),
    "thm:exact-mf-residual": (
        "Malcev residual-finiteness theorem; Shulman, Theorem 10; normal "
        "forms for amalgamated free products",
    ),
    "thm:notes-visible-quotient": (
        "Mal'cev residual-finiteness theorem; Peter--Weyl point separation",
    ),
    "cor:notes-a5-relation": (
        "elementary structure of A_5 and the printed telescope-window "
        "approximation",
    ),
    "thm:mf-arithmetic": (
        "Adian--Rabin theorem; decidability of fixed-dimensional unitary "
        "feasibility over the real closed field",
    ),
}


# Environments of the notes that consume a stated literature input which is
# not itself formalized: (external inputs, coverage gap).
NOTES_LITERATURE_INPUTS: dict[str, tuple[tuple[str, ...], str]] = {
    "thm:torsionfree": (
        (
            "Fournier-Facio, Section 2; Hull, Theorem 7.1; Osin, Lemma 7.1",
        ),
        "The literature input itself is not formalized."),
}


# No single badge in these notes environments includes every printed clause.
NOTES_COLLECTIVE_CLAIMS: set[str] = {
    "cor:marked-obstruction",
    "lem:permanence",
    "thm:notes-spectral-motion",
    "cor:undecidable",
}


# The dependency graph of the notes.  A name that is not a numbered claim of
# the notes is a claim of `non_mf_groups_exist.tex`, resolved through the
# companion manifest by `check_non_mf_claim_manifest.py`.
NOTES_DEPENDENCIES: dict[str, list[str]] = {
    "def:E": [],
    "prop:literal-base-T": ["def:E"],
    "lem:linear": ["def:E"],
    "prop:witness": ["lem:linear", "def:E"],
    "cor:relator-uniform": ["def:E", "cor:marked-obstruction"],
    "thm:signfree": [
        "def:E", "def:invwitness", "thm:collapse", "cor:pullback",
        "prop:witness", "prop:univquot"],
    "thm:reduced": ["lem:faithfultrace", "cor:marked-obstruction"],
    "thm:Esofic": ["def:E", "prop:blocknormalform", "lem:window"],
    "lem:mftrace-group": [],
    "thm:trace": [
        "def:E", "thm:Esofic", "lem:mftrace-group", "cor:marked-obstruction"],
    "thm:transport-variants": [],
    "def:pattern": [],
    "def:invisible": [],
    "thm:criterion": [
        "def:pattern", "thm:transport-variants", "def:invisible"],
    "cor:marked-obstruction": ["prop:witness", "thm:criterion"],
    "cor:generaltransport": ["thm:transport-variants"],
    "thm:compression-radical": ["cor:generaltransport", "thm:criterion"],
    "thm:abstract-nk": ["thm:normal-kazhdan", "def:invisible"],
    "thm:normal-kazhdan": ["def:pattern"],
    "cor:intrinsic-nk": ["thm:abstract-nk", "thm:compression-radical"],
    "thm:exactfd-intrinsic": [],
    "cor:notRFD": ["prop:witness", "def:E", "thm:exactfd-intrinsic"],
    "thm:cyclic": ["def:E", "thm:exactfd-intrinsic"],
    "cor:scaling-family": ["lem:linear"],
    "def:radical": [],
    "lem:portable": ["def:radical", "cor:marked-obstruction"],
    "prop:univquot": ["def:radical"],
    "cor:exactradical": ["def:radical"],
    "cor:pullback": ["lem:portable", "def:radical"],
    "thm:mf-radical-arithmetic": [],
    "thm:fixed-radical-membership": [
        "def:radical", "lem:permanence", "prop:univquot"],
    "thm:fixed-radical-computer": ["def:radical"],
    "cor:nofaithful": ["cor:marked-obstruction", "prop:witness"],
    "lem:permanence": [],
    "cor:quotclosure": ["lem:permanence", "cor:marked-obstruction"],
    "thm:projection-collapse": [],
    "def:invwitness": [],
    "thm:collapse": [
        "def:invwitness", "def:radical", "thm:projection-collapse"],
    "cor:collapsequot": ["thm:collapse", "cor:pullback", "cor:exactradical"],
    "thm:exact-mf-residual": [
        "thm:signfree", "cor:pullback", "cor:exactradical"],
    "thm:notes-spectral-motion": ["thm:projection-collapse"],
    "thm:notes-visible-quotient": ["thm:notes-spectral-motion"],
    "cor:notes-a5-relation": ["thm:notes-visible-quotient"],
    "thm:notes-abelian-boundary": ["thm:notes-spectral-motion"],
    "lem:faithfultrace": [],
    "prop:blocknormalform": [],
    "lem:window": [],
    "prop:horn": ["lem:portable", "cor:marked-obstruction"],
    "cor:undecidable": [],
    "thm:mf-arithmetic": ["cor:undecidable", "lem:permanence"],
    "thm:torsionfree": ["cor:intrinsic-nk", "thm:torsion-free"],
}


@dataclass(frozen=True)
class ProofBoundaries:
    """The reviewed proof-boundary maps of one manuscript."""

    exact_targets: dict[str, tuple[str, str]]
    paper_proofs: dict[str, tuple[str, ...]]
    literature_inputs: dict[str, tuple[tuple[str, ...], str]]
    collective_claims: set[str]
    dependencies: dict[str, list[str]]
    status_policy: str
    paper_identity: str
    paper_identity_with_inputs: str


LITERATURE_IDENTITY = (
    "The printed environment consumes the stated literature input; its "
    "machine-checked inputs are badged in the surrounding discussion.")


BOUNDARIES: dict[str, ProofBoundaries] = {
    "non_mf_groups_exist.tex": ProofBoundaries(
        exact_targets=EXACT_TARGETS,
        paper_proofs=PAPER_PROOFS,
        literature_inputs={},
        collective_claims=COLLECTIVE_CLAIMS,
        dependencies=DEPENDENCIES,
        status_policy=(
            "Every numbered theorem-like environment records its proof "
            "boundary explicitly: an exact Lean counterpart or a complete "
            "paper proof. Exact claims carry exact-role margin declarations; "
            "paper-proved claims carry none."),
        paper_identity="The complete proof is given in the manuscript.",
        paper_identity_with_inputs=(
            "The complete proof is given in the manuscript. Its external "
            "inputs are listed explicitly."),
    ),
    "non_mf_group_notes.tex": ProofBoundaries(
        exact_targets=NOTES_EXACT_TARGETS,
        paper_proofs=NOTES_PAPER_PROOFS,
        literature_inputs=NOTES_LITERATURE_INPUTS,
        collective_claims=NOTES_COLLECTIVE_CLAIMS,
        dependencies=NOTES_DEPENDENCIES,
        status_policy=(
            "Every numbered theorem-like environment records its proof "
            "boundary explicitly: exact Lean counterpart, complete paper "
            "proof, or stated literature input. Exact claims carry exact-role "
            "margin declarations; paper and literature claims carry none."),
        paper_identity="The complete proof is given in the manuscript.",
        paper_identity_with_inputs=(
            "The complete proof is given in the manuscript; its external "
            "inputs are listed explicitly."),
    ),
}


def _check_inventory(claim_ids: set[str], b: ProofBoundaries) -> None:
    maps = (b.exact_targets.keys(), b.paper_proofs.keys(),
            b.literature_inputs.keys())
    overlap = sorted(
        claim for i, first in enumerate(maps) for second in maps[i + 1:]
        for claim in first & second)
    if overlap:
        raise SystemExit(
            f"claims with more than one proof boundary: {', '.join(overlap)}")
    mapped = maps[0] | maps[1] | maps[2]
    missing = sorted(claim_ids - mapped)
    retired = sorted(mapped - claim_ids)
    if missing:
        raise SystemExit(
            f"numbered claims missing proof boundaries: {', '.join(missing)}")
    if retired:
        raise SystemExit(
            f"proof boundaries with no numbered claim: {', '.join(retired)}")
    stray_collective = sorted(b.collective_claims - b.exact_targets.keys())
    if stray_collective:
        raise SystemExit(
            "collective claims with no exact target: " +
            ", ".join(stray_collective))
    dependency_keys = set(b.dependencies)
    if dependency_keys != claim_ids:
        missing_dependencies = sorted(claim_ids - dependency_keys)
        retired_dependencies = sorted(dependency_keys - claim_ids)
        detail = []
        if missing_dependencies:
            detail.append("missing dependency rows: " +
                          ", ".join(missing_dependencies))
        if retired_dependencies:
            detail.append("retired dependency rows: " +
                          ", ".join(retired_dependencies))
        raise SystemExit("; ".join(detail))


def generate(tex: Path) -> dict:
    b = BOUNDARIES.get(tex.name)
    if b is None:
        raise SystemExit(
            f"{tex.name}: no proof-boundary maps; known manuscripts: " +
            ", ".join(sorted(BOUNDARIES)))
    claims = read_printed_claims(tex)
    _check_inventory({claim.claim_id for claim in claims}, b)
    entries = []
    for claim in claims:
        if claim.claim_id in b.paper_proofs or \
                claim.claim_id in b.literature_inputs:
            literature = claim.claim_id in b.literature_inputs
            kind = "literature-input" if literature else "paper-proof"
            if claim.badges:
                raise SystemExit(
                    f"{claim.claim_id}: {kind} claim carries an "
                    "in-environment Lean badge")
            if literature:
                inputs, coverage_gap = b.literature_inputs[claim.claim_id]
                external_inputs = list(inputs)
                if not external_inputs:
                    raise SystemExit(
                        f"{claim.claim_id}: literature-input claim states no "
                        "external input")
                identity = LITERATURE_IDENTITY
            else:
                external_inputs = list(b.paper_proofs[claim.claim_id])
                coverage_gap = ""
                identity = (b.paper_identity_with_inputs if external_inputs
                            else b.paper_identity)
            entries.append({
                "id": claim.claim_id,
                "environment": claim.environment,
                "title": claim.title,
                "statement_sha256": claim.statement_sha256,
                "status": kind,
                "object_identity": identity,
                "dependencies": b.dependencies[claim.claim_id],
                "extra_assumptions": [],
                "external_inputs": external_inputs,
                "coverage_gap": coverage_gap,
                "lean": [],
            })
            continue

        module, declaration = b.exact_targets[claim.claim_id]
        if not claim.badges:
            raise SystemExit(
                f"{claim.claim_id}: exact claim has no margin declaration")
        printed = {(pm, pd) for _role, pm, pd in claim.badges}
        if (module, declaration) not in printed:
            raise SystemExit(
                f"{claim.claim_id}: reviewed exact declaration is not among "
                "the printed margin declarations")
        collective = claim.claim_id in b.collective_claims

        def coverage(pm: str, pd: str) -> str:
            if collective:
                return "one printed clause; the listed declarations are collective"
            if (pm, pd) == (module, declaration):
                return "the complete printed proposition"
            return "a printed conclusion of the proposition"

        entries.append({
            "id": claim.claim_id,
            "environment": claim.environment,
            "title": claim.title,
            "statement_sha256": claim.statement_sha256,
            "status": "exact",
            "object_identity": (
                "The margin declarations collectively cover every printed "
                "clause, with the same literal objects in each clause."
                if collective else
                "The printed environment and the named declaration use the "
                "same literal objects and outer proposition."),
            "dependencies": b.dependencies[claim.claim_id],
            "extra_assumptions": [],
            "external_inputs": [],
            "coverage_gap": "",
            "lean": [{
                "role": "exact",
                "module": pm,
                "declaration": pd,
                "covers": coverage(pm, pd),
            } for pm, pd in dict.fromkeys(
                (pm, pd) for _role, pm, pd in claim.badges)],
        })

    return {
        "schema_version": 1,
        "manuscript": tex.name,
        "status_policy": b.status_policy,
        "claims": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--tex", type=Path, default=REPO / "non_mf_groups_exist.tex")
    parser.add_argument(
        "--output", type=Path,
        default=REPO / "metadata" / "NON_MF_NUMBERED_CLAIMS.json")
    args = parser.parse_args()
    payload = generate(args.tex)
    args.output.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    print(f"wrote {args.output} ({len(payload['claims'])} claims)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
