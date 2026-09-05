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
        "Manuscript/OneSidedMFRadical/LiteralMFClosure",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptMFResidualCalculusLiteral"),
    "thm:compression-criterion": (
        "Manuscript/OneSidedMFRadical/PrintedCriterion",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptOneSidedCompressionCriterion"),
    "thm:headline": (
        "Manuscript/OneSidedMFRadical/ReducedCStarConsequence",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptPrintedHeadline"),
    "lem:stable-finite": (
        "Manuscript/OneSidedMFRadical/StableFiniteness",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptNormMatrixCoronaStableFinite"),
    "lem:kazhdan-projection-order": (
        "Manuscript/OneSidedMFRadical/KazhdanProjectionOrderLiteral",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptLiteralMaximalCStarKazhdanProjectionOrder"),
    "thm:transport": (
        "Manuscript/OneSidedMFRadical/TransportCommutantEquality",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptOneSidedKazhdanTransportCommutantEquality"),
    "cor:defect-hs": (
        "Manuscript/OneSidedMFRadical/DefectHS",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptCompressionDefectHSInvisible"),
    "lem:central-corona-corner": (
        "Manuscript/OneSidedMFRadical/CentralCoronaCorner",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptCentralCoronaCorner"),
    "thm:normal-kazhdan": (
        "Manuscript/OneSidedMFRadical/NormalKazhdan",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptNormalKazhdanRadical"),
    "prop:simple": (
        "Manuscript/OneSidedMFRadical/RankTwelveSimplicity",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint."
        "manuscriptPropositionSimple"),
    "lem:proper-isometry": (
        "Analysis/ProperIsometryStrictOrder",
        "GroupApproximation.manuscriptProperIsometryStrictOrder"),
    "prop:max-infinite": (
        "Analysis/StrictCompressionFromPrinted",
        "GroupApproximation.MaximalCStarPrintedHypotheses."
        "manuscriptMaximalCStarRemarkFromPrintedHypotheses"),
    "thm:factorization-nonmf-trace": (
        "Manuscript/NinetyNineProblems/ProblemXGroups",
        "GroupApproximation.NinetyNineProblems."
        "canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF"),
    "prop:locally-rf-by-z-trace": (
        "Analysis/LocallyRFByIntFactorization",
        "GroupApproximation.LocallyRFByIntFactorization."
        "canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt"),
    "prop:clifford-self-embedding": (
        "Sofic/CliffordWitnessDirectDefect",
        "GroupApproximation.CliffordWitnessDirectDefect."
        "manuscriptMapSignEqOneOfIsOperatorMFTarget"),
}


# These environments deliberately carry no Lean badge.  Their proofs
# are complete in the manuscript.  The tuple lists precisely the outside
# mathematical results used by that proof; an empty tuple means there is no
# additional external input beyond the listed manuscript dependencies.
PAPER_PROOFS: dict[str, tuple[str, ...]] = {
    "thm:full-defect-ring": ("Ershov--Jaikin-Zapirain, Theorem 1.1",),
    "cor:simple-infinite-ring": (),
    "cor:one-sided-ring-maximal": (
        "Ershov--Jaikin-Zapirain, Theorem 1.1",),
    "thm:amenable-trace": (),
    "prop:clifford-locally-rf": ("Elek--Szabo, Theorem 1",),
    "cor:affine-clifford-trace": ("Bekka--de la Harpe--Valette, Example 1.7.4(i)",),
    "lem:commutator-in-defect": (),
    "thm:hull": (
        "Hull, Theorem 7.1",),
    "lem:saturation": (
        "Osin, Lemma 7.1", "Hull, Theorem 3.12",
        "Hull, Corollary 5.7 and Lemma 5.8"),
    "thm:torsion-free": (
        "Fournier-Facio, Section 2", "Hull, Corollary 7.4"),
}


# No single badge in these environments includes every printed clause.
# Their declarations are recorded as collective, with no claim that one
# declaration is a complete wrapper.
COLLECTIVE_CLAIMS: set[str] = {
    "prop:clifford-self-embedding",
    "thm:factorization-nonmf-trace",
}


# The paper-level dependency graph.  Every name is another live numbered
# claim, even when the dependent theorem is printed earlier for exposition.
DEPENDENCIES: dict[str, list[str]] = {
    "prop:mf-residual-calculus": [],
    "thm:compression-criterion": [
        "cor:defect-hs", "thm:normal-kazhdan", "prop:mf-residual-calculus"],
    "thm:full-defect-ring": ["thm:compression-criterion"],
    "thm:headline": [
        "thm:full-defect-ring", "prop:simple",
        "cor:one-sided-ring-maximal"],
    "cor:simple-infinite-ring": ["thm:full-defect-ring"],
    "cor:one-sided-ring-maximal": [
        "thm:full-defect-ring", "prop:max-infinite"],
    "lem:stable-finite": [],
    "lem:kazhdan-projection-order": [],
    "thm:transport": ["lem:stable-finite", "lem:kazhdan-projection-order"],
    "cor:defect-hs": ["thm:transport"],
    "lem:central-corona-corner": [],
    "thm:normal-kazhdan": ["lem:central-corona-corner"],
    "prop:simple": [],
    "lem:proper-isometry": [],
    "prop:max-infinite": [
        "lem:kazhdan-projection-order", "lem:proper-isometry"],
    "thm:factorization-nonmf-trace": [],
    "prop:locally-rf-by-z-trace": [],
    "prop:clifford-self-embedding": ["thm:compression-criterion"],
    "prop:clifford-locally-rf": [
        "prop:clifford-self-embedding", "prop:locally-rf-by-z-trace",
        "thm:factorization-nonmf-trace"],
    "cor:affine-clifford-trace": ["prop:clifford-locally-rf"],
    "thm:amenable-trace": [
        "prop:clifford-locally-rf", "cor:affine-clifford-trace"],
    "thm:hull": [],
    "lem:saturation": ["thm:hull"],
    "lem:commutator-in-defect": [],
    "thm:torsion-free": [
        "thm:compression-criterion", "lem:saturation",
        "lem:commutator-in-defect"],
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
