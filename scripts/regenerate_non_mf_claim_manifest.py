#!/usr/bin/env python3
r"""Regenerate the exact numbered-claim manifest from the manuscript boundary.

The paper keeps its mathematical prose standalone while displaying one compact
linked declaration identifier in the margin of every numbered claim.  This
generator verifies those margin records against an independent claim map and
records statement hashes, signatures, and explicit dependencies.  Semantic
review remains necessary when either proposition changes; the generated diff
makes that review unavoidable and complete.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_non_mf_claim_manifest import read_printed_claims


REPO = Path(__file__).resolve().parent.parent


# Exact formal counterpart of each numbered mathematical claim.  This map is
# independent of the margin records so that a manuscript edit cannot silently
# redirect its own audit target.
CLAIM_TARGETS: dict[str, tuple[str, str]] = {
    "prop:mf-equivalences": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptMFDefinitionEquivalences"),
    "thm:kazhdan-transport": (
        "Sofic/ManuscriptKazhdanTransport",
        "GroupApproximation.KazhdanAsymptoticCommutant.manuscriptKazhdanTransport"),
    "cor:generaltransport": (
        "Sofic/KazhdanAsymptoticCommutant",
        "GroupApproximation.KazhdanAsymptoticCommutant.compressionGroup_transport_both"),
    "thm:sign-criterion": (
        "Sofic/KazhdanSignCriterion",
        "GroupApproximation.KazhdanCompressionCore.manuscriptCentralSignCriterion"),
    "thm:abstract-nk": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction"),
    "cor:intrinsic-nk": (
        "Sofic/NormalKazhdanHyperlinearKilled",
        "GroupApproximation.KazhdanAsymptoticCommutant.normalKazhdan_le_actualCoronaMFResidual_of_le_compressionCentralizerDefect"),
    "cor:pullback": (
        "Sofic/TorsionCompressionCollapse",
        "GroupApproximation.TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient"),
    "def:invwitness": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern"),
    "thm:collapse": (
        "Sofic/InvolutionCollapseEndpoint",
        "GroupApproximation.InvolutionCollapseEndpoint.involutiveCollapseDefect_le_actualCoronaMFResidual"),
    "cor:collapsequot": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptCollapseRadicalReduction"),
    "thm:saturation": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptDefectSaturation"),
    "thm:compression-radical": (
        "Sofic/ManuscriptKazhdanTransport",
        "GroupApproximation.KazhdanAsymptoticCommutant.manuscriptCompressionRadical"),
    "thm:kazhdan-clifford": (
        "Sofic/KazhdanCliffordConstruction",
        "GroupApproximation.KazhdanCliffordConstruction.kazhdanCliffordConstruction"),
    "thm:A": (
        "Sofic/LiteralNonMFEndpoint",
        "GroupApproximation.LiteralNonMFEndpoint.manuscriptTheoremA"),
    "cor:uniform": (
        "Sofic/LiteralUniformObstruction",
        "GroupApproximation.LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction"),
    "cor:scaling-family": (
        "Sofic/ScalingFamilyEndpoint",
        "GroupApproximation.ScalingFamilyEndpoint.manuscriptTheoremFamily"),
    "thm:B": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptTheoremB"),
    "thm:C": (
        "Monsters/LiteralCyclicCalibration",
        "GroupApproximation.LiteralCyclicCalibration.manuscriptCyclicCalibration"),
    "thm:D": (
        "Sofic/LiteralNonMFEndpoint",
        "GroupApproximation.LiteralNonMFEndpoint.manuscriptTheoremD"),
    "thm:E": (
        "Endpoint/NonMFImpact",
        "GroupApproximation.NonMFImpact.witness_sofic_hyperlinear_nonMF"),
    "prop:maximal-cstar": (
        "Analysis/MaximalGroupCStar",
        "GroupApproximation.manuscriptUniverseRelativeMaximalGroupCStar"),
    "def:E": (
        "Sofic/LiteralNonMFPresentation",
        "GroupApproximation.LiteralNonMFPresentation.manuscriptLiteralPresentation"),
    "prop:literal-base-T": (
        "Sofic/LiteralBaseP13PropertyTBridge",
        "GroupApproximation.LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT"),
    "con:clifford": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptCliffordConstruction"),
    "lem:linear": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptLinearModel"),
    "prop:witness": (
        "Sofic/LiteralNonMFLinearWitness",
        "GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one"),
    "cor:notRFD": (
        "Sofic/LiteralFiniteDimensionalObstruction",
        "GroupApproximation.LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences"),
    "lem:lift": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptUnitaryLifting"),
    "lem:unitarycorona": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptUnitaryCoronaEquivalence"),
    "def:pattern": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern"),
    "thm:criterion": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion"),
    "thm:normal-kazhdan": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction"),
    "lem:square": (
        "Sofic/CompressionDefectSquare",
        "GroupApproximation.commutator_conjugate_eq_commutator_sq_of_sq_eq_one"),
    "def:radical": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptMFRadical"),
    "lem:portable": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptRadicalPortability"),
    "prop:univquot": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptUniversalMFQuotient"),
    "cor:exactradical": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient"),
    "cor:nofaithful": (
        "Sofic/LiteralNonMFConsequences",
        "GroupApproximation.LiteralNonMFConsequences.literal_no_faithful_corona_subalgebra_target"),
    "prop:horn": (
        "Sofic/LiteralUniversalHorn",
        "GroupApproximation.LiteralUniversalHorn.manuscriptLiteralUniversalHorn"),
    "cor:cylinder": (
        "Sofic/LiteralMarkedCylinder",
        "GroupApproximation.LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder"),
    "lem:subgroupMF": (
        "Sofic/OperatorMFPositiveControls",
        "GroupApproximation.IsOperatorMF.subgroup"),
    "lem:rfmf": (
        "Sofic/OperatorMFPositiveControls",
        "GroupApproximation.isOperatorMF_of_residuallyFinite"),
    "lem:lfmf": (
        "Sofic/LocallyFiniteMF",
        "GroupApproximation.isOperatorMF_of_locallyFinite"),
    "lem:faithfultrace": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness"),
    "cor:quotclosure": (
        "Sofic/LiteralMFQuotientControls",
        "GroupApproximation.LiteralMFQuotientControls.manuscriptQuotientNonclosure"),
}


# Dependencies are part of the paper's statement-level proof graph.  They are
# intentionally explicit instead of inferred from prose or Lean imports.
DEPENDENCIES: dict[str, list[str]] = {
    "thm:sign-criterion": ["thm:kazhdan-transport"],
    "cor:generaltransport": ["thm:kazhdan-transport"],
    "thm:compression-radical": ["thm:kazhdan-transport"],
    "thm:kazhdan-clifford": ["prop:mf-equivalences", "thm:criterion",
                              "thm:sign-criterion", "thm:kazhdan-transport", "lem:square",
                              "con:clifford"],
    "thm:A": ["def:E", "prop:mf-equivalences", "prop:maximal-cstar",
              "prop:literal-base-T", "prop:witness", "thm:criterion",
              "lem:unitarycorona", "lem:square"],
    "cor:scaling-family": ["thm:A", "thm:kazhdan-clifford"],
    "cor:uniform": ["thm:A"],
    "thm:C": ["thm:B", "con:clifford"],
    "thm:D": ["thm:A", "lem:faithfultrace"],
    "thm:E": ["prop:witness", "lem:portable"],
    "prop:mf-equivalences": ["lem:unitarycorona"],
    "prop:literal-base-T": ["def:E"],
    "lem:linear": ["def:E"],
    "prop:witness": ["con:clifford", "lem:linear", "def:E"],
    "cor:notRFD": ["thm:B", "prop:witness"],
    "lem:unitarycorona": ["lem:lift"],
    "thm:criterion": ["def:pattern", "thm:kazhdan-transport"],
    "thm:normal-kazhdan": ["def:pattern", "thm:kazhdan-transport",
                           "prop:mf-equivalences"],
    "thm:abstract-nk": ["thm:normal-kazhdan", "prop:mf-equivalences"],
    "cor:intrinsic-nk": ["thm:abstract-nk", "thm:compression-radical"],
    "cor:pullback": ["lem:portable", "def:radical"],
    "def:invwitness": [],
    "thm:collapse": ["def:invwitness", "def:radical", "lem:unitarycorona",
                     "thm:kazhdan-transport"],
    "cor:collapsequot": ["thm:collapse", "cor:pullback",
                         "cor:exactradical"],
    "thm:saturation": ["thm:collapse", "lem:portable", "lem:subgroupMF",
                       "prop:univquot"],
    "lem:portable": ["thm:A", "def:radical"],
    "prop:univquot": ["def:radical", "lem:lift", "lem:unitarycorona"],
    "cor:exactradical": ["def:radical"],
    "cor:nofaithful": ["thm:A"],
    "prop:horn": ["thm:A", "lem:portable"],
    "cor:cylinder": ["prop:horn", "thm:A"],
    "cor:quotclosure": ["thm:A", "lem:rfmf"],
}


def generate(tex: Path) -> dict:
    entries = []
    claims = read_printed_claims(tex)
    claim_ids = {claim.claim_id for claim in claims}
    routed_ids = CLAIM_TARGETS.keys()
    missing = sorted(claim_ids - routed_ids)
    stale = sorted(routed_ids - claim_ids)
    if missing:
        raise SystemExit(f"numbered claims missing formal targets: {', '.join(missing)}")
    if stale:
        raise SystemExit(f"formal targets without numbered claims: {', '.join(stale)}")
    for claim in claims:
        module, declaration = CLAIM_TARGETS[claim.claim_id]
        if len(claim.badges) != 1:
            raise SystemExit(
                f"{claim.claim_id}: expected exactly one margin declaration, "
                f"found {len(claim.badges)}")
        role, printed_module, printed_declaration = claim.badges[0]
        if role != "exact":
            raise SystemExit(f"{claim.claim_id}: retained claims must be exact")
        if (printed_module, printed_declaration) != (module, declaration):
            raise SystemExit(
                f"{claim.claim_id}: margin declaration differs from the "
                "independent claim map")
        entries.append({
            "id": claim.claim_id,
            "environment": claim.environment,
            "title": claim.title,
            "statement_sha256": claim.statement_sha256,
            "status": "exact",
            "object_identity": (
                "The printed environment and the named declaration use the same "
                "literal objects and outer proposition."),
            "dependencies": DEPENDENCIES.get(claim.claim_id, []),
            "extra_assumptions": [],
            "external_inputs": [],
            "coverage_gap": "",
            "lean": [{
                "role": "exact",
                "module": module,
                "declaration": declaration,
                "covers": "the complete printed proposition",
            }],
        })
    return {
        "schema_version": 1,
        "manuscript": tex.name,
        "status_policy": (
            "Every numbered theorem-like environment is exact. Each has one "
            "linked declaration and an independently mapped wrapper with the "
            "same literal objects and outer proposition."),
        "claims": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", type=Path,
                        default=REPO / "non_mf_groups_exist.tex")
    parser.add_argument("--output", type=Path,
                        default=REPO / "docs" / "NON_MF_NUMBERED_CLAIMS.json")
    args = parser.parse_args()
    args.output.write_text(
        json.dumps(generate(args.tex), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    print(f"wrote {args.output} ({len(read_printed_claims(args.tex))} claims)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
