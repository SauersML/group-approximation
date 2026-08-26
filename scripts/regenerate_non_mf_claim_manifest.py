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
    "thm:commutant": (
        "Manuscript/OneSidedMFRadical/FiniteDimensionalCommutant",
        "GroupApproximation.Manuscript.OneSidedMFRadical."
        "manuscriptFiniteDimensionalCommutantRigidity"),
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
    "lem:tau-elementary": (
        "Manuscript/OneSidedMFRadical/RankTwelveConfiguration",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint."
        "printedTauGL_mem"),
    "prop:simple": (
        "Manuscript/OneSidedMFRadical/RankTwelveSimplicity",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint."
        "manuscriptPropositionSimple"),
    "prop:defect": (
        "Manuscript/OneSidedMFRadical/RankTwelveConfiguration",
        "GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint."
        "manuscriptPropositionDefect"),
    "prop:mf-upper-bound": (
        "Computability/MFRecognitionPi02",
        "GroupApproximation.MFRecognitionPi02.operatorMFCode_pi02"),
}


# These three environments deliberately carry no Lean badge.  Their proofs
# are complete in the manuscript.  The tuple lists precisely the outside
# mathematical results used by that proof; an empty tuple means the argument
# is entirely elementary and self-contained in the paper.
PAPER_PROOFS: dict[str, tuple[str, ...]] = {
    "prop:leavitt-compression": (
        "Ershov--Jaikin-Zapirain, Theorem 1.1",),
    "lem:local-models": (
        "Korchagin, Proposition 7 (amplification of the separation constant)",),
    "lem:marked-closed": (),
    "lem:rf-regular": (),
    "thm:hnn-permanence": (
        "Ueda, Proposition 2.4 (the universal HNN corner construction)",
        "Shulman, Theorem 20 (the amalgam criterion for MF)",
        "Britton's lemma",),
    "cor:central-hnn": (),
    "lem:seed": (
        "Leavitt's normal form: the monomials without a factor s_1 t_1 are "
        "an F_2-basis of L(1,2)",),
    "lem:switch": (
        "Bilanovic--Chubb--Roven, Theorem 3.1 (the construction pattern)",),
    "lem:bridge": (
        "Britton's lemma", "Reidemeister--Schreier rewriting",
        "free basis of the normal closure of a basis element",),
    "lem:mikhailova": (
        "Higman's embedding theorem in Mikaelian's explicit form",
        "Mikhailova's fibre product",),
    "lem:central-rope": ("Britton's lemma",),
    "lem:finite-rope": (),
    "lem:negative-branch": ("Britton's lemma",),
    "thm:recognition": (
        "Soare: INF is Pi^0_2-complete and FIN is Sigma^0_2-complete",),
    "lem:reduced-products": (
        "Blackadar--Kirchberg: the standard diagonal permanence argument",
        "Korchagin, proof of Proposition 6",),
    "lem:tensor-sync": (),
    "lem:positive-branch": (),
}


# No single badge in this environment includes every printed clause.  The
# two declarations printed there are therefore recorded as collective rather
# than pretending that either is a complete wrapper.
COLLECTIVE_CLAIMS: set[str] = set()


# The paper-level dependency graph.  Every name is another live numbered
# claim, even when the dependent theorem is printed earlier for exposition.
DEPENDENCIES: dict[str, list[str]] = {
    "prop:mf-residual-calculus": ["lem:central-corona-corner"],
    "thm:compression-criterion": [
        "thm:commutant", "cor:defect-hs", "thm:normal-kazhdan"],
    "thm:headline": [
        "thm:compression-criterion", "prop:leavitt-compression",
        "prop:simple", "prop:defect"],
    "thm:commutant": [],
    "lem:stable-finite": [],
    "lem:kazhdan-projection-order": [],
    "thm:transport": ["lem:stable-finite", "lem:kazhdan-projection-order"],
    "cor:defect-hs": ["thm:transport"],
    "lem:central-corona-corner": [],
    "thm:normal-kazhdan": ["lem:central-corona-corner"],
    "lem:tau-elementary": [],
    "prop:leavitt-compression": ["lem:tau-elementary"],
    "prop:simple": [],
    "prop:defect": [],
    "lem:local-models": [],
    "prop:mf-upper-bound": ["lem:local-models"],
    "lem:marked-closed": ["lem:local-models"],
    "lem:rf-regular": [],
    "thm:hnn-permanence": [],
    "cor:central-hnn": ["thm:hnn-permanence"],
    "lem:seed": [],
    "lem:switch": ["lem:seed"],
    "lem:bridge": [],
    "lem:mikhailova": ["lem:switch", "lem:bridge"],
    "lem:central-rope": ["lem:mikhailova", "lem:bridge"],
    "lem:finite-rope": ["lem:central-rope"],
    "lem:negative-branch": [
        "lem:switch", "lem:bridge", "lem:finite-rope", "thm:headline"],
    "thm:recognition": [
        "prop:mf-upper-bound", "lem:finite-rope", "lem:positive-branch",
        "lem:negative-branch"],
    "lem:reduced-products": [],
    "lem:tensor-sync": ["lem:reduced-products", "thm:hnn-permanence"],
    "lem:positive-branch": [
        "lem:finite-rope", "lem:tensor-sync", "lem:central-rope",
        "lem:rf-regular", "cor:central-hnn", "lem:bridge"],
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
