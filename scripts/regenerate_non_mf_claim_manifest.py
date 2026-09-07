#!/usr/bin/env python3
r"""Regenerate the numbered-claim manifest for the non-MF manuscript.

The independent maps below are the reviewed boundary between the current
printed claims and their proofs.  An exact claim names one current Lean
declaration that states the whole proposition.  A paper-proved claim records
the external inputs consumed by the complete proof printed in the manuscript.
The generator also records every additional exact badge printed in the same
environment, so a multi-conclusion statement cannot hide an unreviewed badge.
"""

from __future__ import annotations

import argparse
import json
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
        "manuscriptOneSidedRingMaximalIsometryRankTwoAllCharacteristics"),
    "thm:amenable-trace": (
        "Manuscript/OneSidedMFRadical/AmenableTraceTheorem",
        "GroupApproximation.AmenableTraceTheorem."
        "manuscriptAmenableNonquasidiagonalTrace"),
    "prop:clifford-locally-rf": (
        "Sofic/CliffordWitnessSoficPrinted",
        "GroupApproximation.AmenableTraceTheorem.manuscriptCliffordLocallyRF"),
    "prop:linear-collapse": (
        "Manuscript/OneSidedMFRadical/QuantitativeCollapse",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "QuantitativeCollapse.manuscriptLinearCollapse"),
    "lem:two-copies": (
        "Manuscript/OneSidedMFRadical/RankDescentPrintedLemmas",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted."
        "manuscriptTwoCopiesLemma"),
    "lem:rank-two": (
        "Manuscript/OneSidedMFRadical/RankDescentPrintedLemmas",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted."
        "manuscriptRankTwoNormalGeneration"),
}


# These environments deliberately carry no Lean badge.  Their proofs
# are complete in the manuscript.  The tuple lists precisely the outside
# mathematical results used by that proof; an empty tuple means there is no
# additional external input beyond the listed manuscript dependencies.
PAPER_PROOFS: dict[str, tuple[str, ...]] = {
    # The spectral tensor argument and the wordwise compactness theorem
    # have complete written proofs, without new Lean verification badges.
    "lem:linear-tensor-amplification": (),
    "thm:word-linear-certificate": (),
    # The finite-block theorem has a full written proof. Its new analytic
    # step is not yet a compiled Lean endpoint; do not inherit older badges.
    "thm:finite-algebra-transport": (
        "Finite-dimensional C*-algebra structure and compact Haar integration",),
    "thm:perfect-block-radical": (
        "Free-product normal form, free tree actions, and residual finiteness of free groups",
        "Elek--Szabo, Theorem 1"),
    "thm:fp-sofic-radical": (
        "Bekka--de la Harpe--Valette, Example 1.7.4(i)",
        "LiteralBaseCompleteness.baseAffineEquiv (existing in-repository base presentation)",
        "Simplicity and perfection of A_5; free-product center theorem"),
    # `thm:full-defect-ring` moved to EXACT_TARGETS 2026-09-07:
    # `PropertyT/IntegralColumnPlaneClosure.lean` closed
    # `FinitelyGeneratedRingGeneralRankElementaryPropertyT` unconditionally
    # (commit 343a1c4a4), and `FullDefectRingEJZUnconditional.lean` spends it,
    # so the corollaries below no longer carry any external input either --
    # both proofs just say "Theorem thm:full-defect-ring applies", which is
    # now unconditional.  `cor:simple-infinite-ring` and
    # `cor:one-sided-ring-maximal` moved to EXACT_TARGETS the same day, once
    # badge batch 3 gave both hypothesis-free n>=2 carriers.
    # `thm:amenable-trace` and `prop:clifford-locally-rf` moved to
    # EXACT_TARGETS 2026-09-07 (badges landed:
    # AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTrace,
    # AmenableTraceTheorem.manuscriptCliffordLocallyRF in
    # Sofic/CliffordWitnessSoficPrinted.lean).
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
    "cor:relative-quotient": ("Hull, Corollary 7.4",),
    "cor:regular-nonmf-algebra": (
        "Osin, Theorem 1.2", "Dahmani--Guirardel--Osin, Theorem 2.35",
        "Gerasimova--Osin, Theorem 1.1"),
    # `lem:two-copies` and `lem:rank-two` are EXACT_TARGETS, not here (both
    # badged: RankDescentPrintedLemmas.manuscriptTwoCopiesLemma /
    # .manuscriptRankTwoNormalGeneration).
    # `thm:leavitt-mf-quotient` was replaced 2026-09-07 by the general
    # `thm:mf-quotient-units` plus the Leavitt-specific `cor:leavitt-mf-quotient`.
    "thm:mf-quotient-units": (
        "Ara--Goodearl--Pardo, Corollary 1.7, Proposition 1.5, and Theorem 2.4",
        "Menal--Moncasi, proof of Theorem 2.2 and the remark after Corollary 2.3",
        "Blackadar--Kirchberg"),
    "cor:leavitt-mf-quotient": ("Khanh--Thanh, proof of Theorem 7.2",),
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
    # `prop:linear-collapse` prints one badge per direction of its "Then ...
    # Conversely ..." statement (manuscriptLinearCollapse /
    # manuscriptLinearCollapseConverse); neither alone is the whole
    # proposition.
    "prop:linear-collapse",
    # `cor:simple-infinite-ring` prints one badge per sentence
    # (manuscriptSimpleInfiniteRingRankTwoAllCharacteristics /
    # manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics).
    "cor:simple-infinite-ring",
    # `cor:one-sided-ring-maximal` prints four badges: the n>=4 isometry
    # clause, the n>=2 isometry clause, the n>=2 reduced-C*-algebra clause,
    # and the unit-group-not-MF clause; no single one is the whole
    # corollary.
    "cor:one-sided-ring-maximal",
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
    "prop:clifford-locally-rf": [
        "prop:clifford-self-embedding", "prop:locally-rf-by-z-trace",
        "thm:factorization-nonmf-trace"],
    "thm:amenable-trace": ["prop:clifford-locally-rf"],
    "thm:finite-algebra-transport": [
        "thm:transport", "prop:mf-residual-calculus"],
    "thm:perfect-block-radical": [
        "thm:finite-algebra-transport", "prop:mf-residual-calculus",
        "prop:locally-rf-by-z-trace", "thm:factorization-nonmf-trace"],
    "thm:fp-sofic-radical": ["thm:perfect-block-radical"],
    "thm:hull": [],
    "lem:saturation": ["thm:hull"],
    "thm:torsion-free": [
        "thm:compression-criterion", "lem:saturation"],
    "lem:linear-tensor-amplification": [],
    "thm:word-linear-certificate": [
        "lem:linear-tensor-amplification", "prop:mf-residual-calculus",
        "lem:stable-finite"],
    "prop:linear-collapse": ["thm:word-linear-certificate"],
    "cor:relative-quotient": ["thm:torsion-free", "thm:hull"],
    "cor:regular-nonmf-algebra": ["thm:torsion-free"],
}


def _check_inventory(claim_ids: set[str]) -> None:
    mapped = EXACT_TARGETS.keys() | PAPER_PROOFS.keys()
    missing = sorted(claim_ids - mapped)
    retired = sorted(mapped - claim_ids)
    if missing:
        raise SystemExit(
            f"numbered claims missing proof boundaries: {', '.join(missing)}")
    if retired:
        raise SystemExit(
            f"proof boundaries with no numbered claim: {', '.join(retired)}")
    dependency_keys = set(DEPENDENCIES)
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
    claims = read_printed_claims(tex)
    _check_inventory({claim.claim_id for claim in claims})
    entries = []
    for claim in claims:
        if claim.claim_id in PAPER_PROOFS:
            if claim.badges:
                raise SystemExit(
                    f"{claim.claim_id}: paper-proof claim carries an "
                    "in-environment Lean badge")
            external_inputs = list(PAPER_PROOFS[claim.claim_id])
            identity = "The complete proof is given in the manuscript."
            if external_inputs:
                identity += " Its external inputs are listed explicitly."
            entries.append({
                "id": claim.claim_id,
                "environment": claim.environment,
                "title": claim.title,
                "statement_sha256": claim.statement_sha256,
                "status": "paper-proof",
                "object_identity": identity,
                "dependencies": DEPENDENCIES[claim.claim_id],
                "extra_assumptions": [],
                "external_inputs": external_inputs,
                "coverage_gap": "",
                "lean": [],
            })
            continue

        module, declaration = EXACT_TARGETS[claim.claim_id]
        if not claim.badges:
            raise SystemExit(
                f"{claim.claim_id}: exact claim has no margin declaration")
        printed = {(pm, pd) for _role, pm, pd in claim.badges}
        if (module, declaration) not in printed:
            raise SystemExit(
                f"{claim.claim_id}: reviewed exact declaration is not among "
                "the printed margin declarations")
        collective = claim.claim_id in COLLECTIVE_CLAIMS

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
            "dependencies": DEPENDENCIES[claim.claim_id],
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
        "status_policy": (
            "Every numbered theorem-like environment records its proof "
            "boundary explicitly: an exact Lean counterpart or a complete "
            "paper proof. Exact claims carry exact-role margin declarations; "
            "paper-proved claims carry none."),
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
