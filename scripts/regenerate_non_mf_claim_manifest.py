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
        "Sofic/KazhdanTransportAnyUniverse",
        "GroupApproximation.KazhdanAsymptoticCommutant."
        "manuscriptKazhdanTransport_anyUniverse"),
    "cor:generaltransport": (
        "Sofic/DefectActionAnyUniverse",
        "GroupApproximation.KazhdanAsymptoticCommutant.compressionGroup_transport_both_anyUniverse"),
    "thm:sign-criterion": (
        "Sofic/CentralSignAnyUniverse",
        "GroupApproximation.KazhdanCompressionCore.manuscriptCentralSignCriterion_anyUniverse"),
    "thm:abstract-nk": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction"),
    "cor:intrinsic-nk": (
        "Sofic/NormalKazhdanAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanRadical_anyUniverse"),
    "cor:pullback": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient"),
    "def:invwitness": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern"),
    "thm:collapse": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapse"),
    "cor:collapsequot": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptCollapseRadicalReduction"),
    "thm:compression-radical": (
        "Sofic/DefectRadicalAnyUniverse",
        "GroupApproximation.KazhdanAsymptoticCommutant.manuscriptCompressionRadical_anyUniverse"),
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
    # Renamed 2026-08-16 away from letter-shaped labels: `mainthm` numbers by
    # position, so `thm:D` printed as Theorem C and `thm:E` as Theorem D, while
    # `thm:B` and `thm:C` were not lettered theorems at all.  The manuscript
    # keeps the old spellings as second labels on the same environments, so
    # in-flight `\ref`s still resolve; these keys follow the FIRST label, which
    # is what `read_printed_claims` reads.
    "thm:exactfd": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptTheoremB"),
    "thm:exactfd-intrinsic": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptTheoremB",
    ),
    "thm:cyclic": (
        "Monsters/LiteralCyclicCalibration",
        "GroupApproximation.LiteralCyclicCalibration.manuscriptCyclicCalibration"),
    "thm:reduced": (
        "Sofic/LiteralNonMFEndpoint",
        "GroupApproximation.LiteralNonMFEndpoint.manuscriptTheoremD"),
    "thm:Esofic": (
        "Sofic/LiteralSoficAssembly",
        "GroupApproximation.LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF"),
    "lem:mftrace-group": (
        "Sofic/TraceSeparationEndpoint",
        "GroupApproximation.manuscriptMFTraceGroupBridge"),
    "thm:trace": (
        "Sofic/TraceSeparationEndpoint",
        "GroupApproximation.manuscriptTraceSeparation"),
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
    "lem:finitecompare": (
        "Sofic/UltraproductKazhdanTransport",
        "GroupApproximation.kt_10_finiteness_reverses"),
    "lem:ultrafinite": (
        "Sofic/UltraproductDedekindFinite",
        "GroupApproximation.kt_06_ultraproduct_finite"),
    "prop:blocknormalform": (
        "Sofic/LiteralBlockNormalForm",
        "GroupApproximation.LiteralBlockNormalForm.markedGroupEquivModel"),
    "lem:window": (
        "Sofic/BlockCliffordTowerSofic",
        "GroupApproximation.BlockCliffordTowerSofic.manuscriptResiduallyFiniteWindow"),
    "cor:undecidable": (
        "Computability/BooneWordProblemUndecidable",
        "GroupApproximation.Computability."
        "operatorMF_recognition_not_computable"),
    "def:invisible": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptHSInvisibleCharacterization",
    ),
    "prop:proper-isometry": (
        "Analysis/ProperIsometryStrictOrder",
        "GroupApproximation.manuscriptProperIsometryStrictOrder",
    ),
    "thm:signfree": (
        "Sofic/LiteralSignFreeQuotient",
        "GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF",
    ),
    "thm:signfree": (
        "Sofic/LiteralSignFreeQuotient",
        "GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF",
    ),
    "thm:transport-variants": (
        "Sofic/TransportVariantsAnyUniverse",
        "GroupApproximation.TransportVariantsAnyUniverse."
        "scaled_transport_both_anyUniverse",
    ),
    "thm:markedclosed": (
        "Sofic/MarkedMFClosed",
        "GroupApproximation.MarkedGroupSpace.isClosed_operatorMFLocus",
    ),
    "thm:projection-collapse": (
        "Sofic/ProjectionCompressionCollapse",
        "GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse",
    ),
    "lem:permanence": (
        "Sofic/OperatorMFPositiveControls",
        "GroupApproximation.IsOperatorMF.subgroup",
    ),
    "def:pattern": (
        "Sofic/ConjugationDatumAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern_anyUniverse"),
    "thm:criterion": (
        "Sofic/FiniteNormalAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion_anyUniverse"),
    "thm:normal-kazhdan": (
        "Sofic/NormalKazhdanAnyUniverse",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction_anyUniverse"),
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
    "lem:permanence": (
        "Sofic/OperatorMFPositiveControls",
        "GroupApproximation.IsOperatorMF.subgroup"),
    "lem:permanence": (
        "Sofic/OperatorMFPositiveControls",
        "GroupApproximation.isOperatorMF_of_residuallyFinite"),
    "lem:permanence": (
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
    "thm:exactfd-intrinsic": ["thm:exactfd"],
    "thm:cyclic": ["thm:exactfd", "con:clifford"],
    "thm:reduced": ["thm:A", "lem:faithfultrace"],
    "thm:Esofic": ["def:E", "thm:A", "prop:blocknormalform", "lem:window"],
    "lem:mftrace-group": [],
    "thm:trace": ["thm:A", "def:E", "thm:Esofic", "lem:mftrace-group"],
    "prop:mf-equivalences": ["lem:unitarycorona"],
    "prop:literal-base-T": ["def:E"],
    "lem:linear": ["def:E"],
    "prop:witness": ["con:clifford", "lem:linear", "def:E"],
    "cor:notRFD": ["thm:exactfd", "prop:witness"],
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
    "thm:signfree": ["def:E", "def:invwitness", "thm:collapse",
                     "cor:pullback", "prop:witness", "prop:univquot",
                     "thm:kazhdan-clifford"],
    "lem:portable": ["thm:A", "def:radical"],
    "prop:univquot": ["def:radical", "lem:lift", "lem:unitarycorona"],
    "cor:exactradical": ["def:radical"],
    "cor:nofaithful": ["thm:A"],
    "prop:horn": ["thm:A", "lem:portable"],
    "cor:quotclosure": ["thm:A", "lem:permanence"],
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
        if module == "LITERATURE":
            if claim.badges:
                raise SystemExit(
                    f"{claim.claim_id}: literature-input claims carry no "
                    "in-environment margin declaration")
            entries.append({
                "id": claim.claim_id,
                "environment": claim.environment,
                "title": claim.title,
                "statement_sha256": claim.statement_sha256,
                "status": "literature-input",
                "object_identity": (
                    "The printed environment consumes the stated literature "
                    "input; its machine-checked inputs are badged in the "
                    "surrounding discussion."),
                "dependencies": DEPENDENCIES.get(claim.claim_id, []),
                "extra_assumptions": [],
                "external_inputs": [declaration],
                "coverage_gap": (
                    "The literature input itself is not formalized."),
                "lean": [],
            })
            continue
        if not claim.badges:
            raise SystemExit(
                f"{claim.claim_id}: expected at least one margin declaration")
        for role, _pm, _pd in claim.badges:
            if role != "exact":
                raise SystemExit(
                    f"{claim.claim_id}: retained claims must be exact")
        printed = {(pm, pd) for _r, pm, pd in claim.badges}
        if (module, declaration) not in printed:
            raise SystemExit(
                f"{claim.claim_id}: the independently mapped declaration is "
                "not among the printed margin declarations")
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
                "module": pm,
                "declaration": pd,
                "covers": (
                    "the complete printed proposition"
                    if (pm, pd) == (module, declaration)
                    else "a printed conclusion of the proposition"),
            } for _r, pm, pd in claim.badges],
        })
    return {
        "schema_version": 1,
        "manuscript": tex.name,
        "status_policy": (
            "Every numbered theorem-like environment is exact. Each carries "
            "exact-role margin declarations, one of which is the "
            "independently mapped wrapper with the same literal objects and "
            "outer proposition."),
        "claims": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", type=Path,
                        default=REPO / "non_mf_groups_exist.tex")
    parser.add_argument("--output", type=Path,
                        default=REPO / "metadata" / "NON_MF_NUMBERED_CLAIMS.json")
    args = parser.parse_args()
    args.output.write_text(
        json.dumps(generate(args.tex), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    print(f"wrote {args.output} ({len(read_printed_claims(args.tex))} claims)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
