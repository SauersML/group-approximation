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
    "lem:tensor-amplification": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptTensorAmplification"),
    "thm:kazhdan-transport": (
        "Sofic/ManuscriptSubgroupSpecializations",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptKazhdanTransportSubgroup"),
    "cor:generaltransport": (
        "Sofic/DefectActionAnyUniverse",
        "GroupApproximation.KazhdanAsymptoticCommutant.compressionGroup_transport_both_anyUniverse"),
    "thm:sign-criterion": (
        "Sofic/ManuscriptSubgroupSpecializations",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptCentralSignCriterionSubgroup"),
    "lem:corner": (
        "Analysis/PrintedCornerCompression",
        "GroupApproximation.PrintedCornerCompression."
        "manuscriptCornerAsymptoticRepresentation"),
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
    "cor:relator-uniform": (
        "Sofic/LiteralRelatorObstruction",
        "GroupApproximation.LiteralRelatorObstruction."
        "literal_relator_uniform_obstruction"),
    "cor:scaling-family": (
        "Sofic/ScalingFamilyEndpoint",
        "GroupApproximation.ScalingFamilyEndpoint.manuscriptTheoremFamily"),
    # Renamed 2026-08-16 away from letter-shaped labels because `mainthm`
    # letters depend on position.  These stable keys name the mathematical
    # content and are the labels read by `read_printed_claims`.
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
        "GroupApproximation.LiteralSoficAssembly.markedGroup_isSofic"),
    "lem:mftrace-group": (
        "Sofic/TraceSeparationEndpoint",
        "GroupApproximation.manuscriptMFTraceGroupBridge"),
    "thm:trace": (
        "Sofic/TraceSeparationEndpoint",
        "GroupApproximation.manuscriptTraceSeparation"),
    "prop:maximal-cstar": (
        "Analysis/MaximalCStarAllUniverses",
        "GroupApproximation.manuscriptMaximalGroupCStarUniversalProperty"),
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
    "lem:kazhdan-gap": (
        "Sofic/UltraproductKazhdanProjection",
        "GroupApproximation.UltraproductKazhdanProjection."
        "manuscriptKazhdanSpectralGap",
    ),
    "lem:corner": (
        "Analysis/PrintedCornerCompression",
        "GroupApproximation.PrintedCornerCompression."
        "manuscriptCornerAsymptoticRepresentation",
    ),
    "rem:maxinfinite": (
        "Analysis/StrictCompressionFromPrinted",
        "GroupApproximation.MaximalCStarPrintedHypotheses."
        "manuscriptMaximalCStarRemarkFromPrintedHypotheses",
    ),
    "thm:signfree": (
        "Sofic/LiteralSignFreeQuotient",
        "GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF",
    ),
    "thm:transport-variants": (
        "Sofic/ManuscriptSubgroupSpecializations",
        "GroupApproximation.ManuscriptExactWrappers."
        "manuscriptWeightedTransportSubgroup",
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
    "lem:faithfultrace": (
        "Sofic/ManuscriptExactWrappers",
        "GroupApproximation.ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness"),
    "cor:quotclosure": (
        "Sofic/LiteralMFQuotientControls",
        "GroupApproximation.LiteralMFQuotientControls.manuscriptQuotientNonclosure"),
    "thm:exact-mf-residual": (
        "PAPER",
        "Malcev residual-finiteness theorem; Shulman, Theorem 10; "
        "normal forms for amalgamated free products"),
    "thm:torsionfree": (
        "LITERATURE",
        "Fournier-Facio, Section 2; Hull, Theorem 7.1; Osin, Lemma 7.1"),
}


# Numbered claims whose formal counterpart intentionally uses different
# binders are recorded here.  The current manuscript subgroup statements now
# have literal subgroup-coordinate wrappers, so this table is empty.
SPECIALIZATION_IDENTITIES: dict[str, str] = {
    "thm:A": (
        "The companion notes identify the printed affine construction with "
        "the literal presented group used by the named declarations; the "
        "printed conclusions are invariant under that identification."),
    "cor:uniform": (
        "The companion notes identify the printed affine construction with "
        "the literal presented group used by the named declaration, carrying "
        "the distinguished element and the local obstruction with it."),
}


# No single declaration states these enumerated claims as one conjunction;
# their margin declarations cover the printed clauses collectively.
COLLECTIVE_CLAIMS = {"lem:permanence", "cor:undecidable"}


# Dependencies are part of the paper's statement-level proof graph.  They are
# intentionally explicit instead of inferred from prose or Lean imports.
DEPENDENCIES: dict[str, list[str]] = {
    "thm:sign-criterion": ["thm:kazhdan-transport"],
    "cor:generaltransport": ["thm:kazhdan-transport"],
    "thm:compression-radical": ["thm:kazhdan-transport"],
    "thm:kazhdan-clifford": ["prop:mf-equivalences",
                              "thm:sign-criterion", "thm:kazhdan-transport",
                              "con:clifford"],
    "thm:A": ["thm:kazhdan-clifford", "lem:unitarycorona"],
    "cor:scaling-family": ["thm:A", "thm:kazhdan-clifford"],
    "cor:uniform": ["thm:A"],
    "cor:relator-uniform": ["thm:A", "def:E", "lem:unitarycorona"],
    "thm:exactfd-intrinsic": ["thm:exactfd"],
    "thm:cyclic": ["thm:exactfd", "con:clifford"],
    "thm:reduced": ["thm:A", "lem:faithfultrace"],
    "thm:Esofic": ["def:E", "prop:blocknormalform", "lem:window"],
    "lem:mftrace-group": [],
    "thm:trace": ["thm:A", "def:E", "thm:Esofic", "lem:mftrace-group"],
    "prop:mf-equivalences": ["lem:unitarycorona", "lem:tensor-amplification"],
    "lem:tensor-amplification": [],
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
    "lem:corner": ["lem:lift"],
    "lem:kazhdan-gap": [],
    "rem:maxinfinite": ["prop:proper-isometry", "prop:maximal-cstar"],
    "prop:horn": ["thm:A", "lem:portable"],
    "cor:quotclosure": ["thm:A", "lem:permanence"],
    "thm:exact-mf-residual": ["thm:signfree", "cor:pullback",
                               "cor:exactradical"],
    "thm:torsionfree": ["cor:intrinsic-nk"],
}


def generate(tex: Path) -> dict:
    entries = []
    claims = read_printed_claims(tex)
    claim_ids = {claim.claim_id for claim in claims}
    missing = sorted(claim_ids - CLAIM_TARGETS.keys())
    if missing:
        raise SystemExit(f"numbered claims missing formal targets: {', '.join(missing)}")
    for claim in claims:
        module, declaration = CLAIM_TARGETS[claim.claim_id]
        if module in {"PAPER", "LITERATURE"}:
            if claim.badges:
                raise SystemExit(
                    f"{claim.claim_id}: non-Lean claims carry no "
                    "in-environment margin declaration")
            paper_proof = module == "PAPER"
            entries.append({
                "id": claim.claim_id,
                "environment": claim.environment,
                "title": claim.title,
                "statement_sha256": claim.statement_sha256,
                "status": "paper-proof" if paper_proof else "literature-input",
                "object_identity": (
                    "The complete proof is given in the manuscript; its "
                    "external inputs are listed explicitly."
                    if paper_proof else
                    "The printed environment consumes the stated literature "
                    "input; its machine-checked inputs are badged in the "
                    "surrounding discussion."),
                "dependencies": DEPENDENCIES.get(claim.claim_id, []),
                "extra_assumptions": [],
                "external_inputs": [declaration],
                "coverage_gap": (
                    "" if paper_proof else
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
        if claim.claim_id in SPECIALIZATION_IDENTITIES:
            object_identity = SPECIALIZATION_IDENTITIES[claim.claim_id]
        elif claim.claim_id in COLLECTIVE_CLAIMS:
            object_identity = (
                "The margin declarations collectively cover every printed "
                "clause, with the same literal objects in each clause.")
        else:
            object_identity = (
                "The printed environment and the named declaration use the same "
                "literal objects and outer proposition.")

        def coverage(pm: str, pd: str) -> str:
            if claim.claim_id in SPECIALIZATION_IDENTITIES:
                if (pm, pd) == (module, declaration):
                    return (
                        "the complete printed proposition under the "
                        "specialization or identification recorded above")
                return "a printed conclusion of the proposition"
            if claim.claim_id in COLLECTIVE_CLAIMS:
                return "one printed clause; the listed declarations are collective"
            return (
                "the complete printed proposition"
                if (pm, pd) == (module, declaration)
                else "a printed conclusion of the proposition")

        entries.append({
            "id": claim.claim_id,
            "environment": claim.environment,
            "title": claim.title,
            "statement_sha256": claim.statement_sha256,
            "status": "exact",
            "object_identity": object_identity,
            "dependencies": DEPENDENCIES.get(claim.claim_id, []),
            "extra_assumptions": [],
            "external_inputs": [],
            "coverage_gap": "",
            "lean": [{
                "role": "exact",
                "module": pm,
                "declaration": pd,
                "covers": coverage(pm, pd),
            } for _r, pm, pd in claim.badges],
        })
    return {
        "schema_version": 1,
        "manuscript": tex.name,
        "status_policy": (
            "Every numbered theorem-like environment records its proof "
            "boundary explicitly: exact Lean counterpart, complete paper "
            "proof, or stated literature input. Exact claims carry exact-role "
            "margin declarations; paper and literature claims carry none."),
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
