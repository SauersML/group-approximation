#!/usr/bin/env python3
r"""Regenerate the numbered-claim manifest for the spectral-compression paper."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_non_mf_claim_manifest import read_printed_claims


REPO = Path(__file__).resolve().parent.parent


# The map is intentionally restricted to claims in the current paper.  Keeping
# retired manuscript declarations here would make a stale proof architecture
# look live to the audit.
CLAIM_TARGETS: dict[str, tuple[str, str]] = {
    "thm:headline": (
        "Sofic/AlternatingLampExactRadical",
        "GroupApproximation.AlternatingLampFamily.alternatingFamilyPackage",
    ),
    "thm:spectral": (
        "Analysis/SpectralComponentDiameter",
        "GroupApproximation.SpectralComponentDiameter."
        "norm_sub_le_of_same_clopen_spectral_pieces",
    ),
    "thm:visible": (
        "Sofic/FinitePerfectLampExactRadical",
        "GroupApproximation.FinitePerfectLamp.finitePerfectPackage",
    ),
    "thm:fd-defect": (
        "Criterion/CompressionCentralizerDefect",
        "GroupApproximation.compressionCentralizerDefect_le_ker",
    ),
    "thm:projection-collapse": (
        "Sofic/ProjectionCompressionCollapse",
        "GroupApproximation.ProjectionCompressionCollapse."
        "corona_projection_collapse",
    ),
    "prop:factor": (
        "Sofic/FinitePerfectLampExactRadical",
        "GroupApproximation.FinitePerfectLamp."
        "actualCoronaMFResidual_eq_lampSub",
    ),
}


COLLECTIVE_CLAIMS = {
    "thm:headline",
    "thm:spectral",
    "thm:visible",
    "prop:factor",
}


DEPENDENCIES: dict[str, list[str]] = {
    "thm:headline": ["thm:visible"],
    "thm:spectral": ["thm:projection-collapse"],
    "thm:visible": ["thm:spectral"],
    "thm:fd-defect": [],
    "thm:projection-collapse": [],
    "prop:factor": ["thm:spectral"],
}


def generate(tex: Path) -> dict:
    entries = []
    claims = read_printed_claims(tex)
    claim_ids = {claim.claim_id for claim in claims}
    missing = sorted(claim_ids - CLAIM_TARGETS.keys())
    if missing:
        raise SystemExit(
            f"numbered claims missing formal targets: {', '.join(missing)}"
        )
    stale = sorted(CLAIM_TARGETS.keys() - claim_ids)
    if stale:
        raise SystemExit(
            f"formal targets remain for retired claims: {', '.join(stale)}"
        )

    for claim in claims:
        module, declaration = CLAIM_TARGETS[claim.claim_id]
        if not claim.badges:
            raise SystemExit(
                f"{claim.claim_id}: expected at least one margin declaration"
            )
        if any(role != "exact" for role, _pm, _pd in claim.badges):
            raise SystemExit(
                f"{claim.claim_id}: retained claims must use exact badges"
            )
        printed = {(pm, pd) for _role, pm, pd in claim.badges}
        if (module, declaration) not in printed:
            raise SystemExit(
                f"{claim.claim_id}: independently mapped declaration is not "
                "among the printed badges"
            )

        collective = claim.claim_id in COLLECTIVE_CLAIMS
        entries.append(
            {
                "id": claim.claim_id,
                "environment": claim.environment,
                "title": claim.title,
                "statement_sha256": claim.statement_sha256,
                "status": "exact",
                "object_identity": (
                    "The margin declarations collectively cover every printed "
                    "clause on the same literal groups and maps."
                    if collective
                    else "The printed environment and named declaration use "
                    "the same literal objects and proposition."
                ),
                "dependencies": DEPENDENCIES[claim.claim_id],
                "extra_assumptions": [],
                "external_inputs": [],
                "coverage_gap": "",
                "lean": [
                    {
                        "role": "exact",
                        "module": pm,
                        "declaration": pd,
                        "covers": (
                            "one printed clause; the declarations are collective"
                            if collective
                            else "the complete printed proposition"
                        ),
                    }
                    for _role, pm, pd in claim.badges
                ],
            }
        )

    return {
        "schema_version": 1,
        "manuscript": tex.name,
        "status_policy": (
            "Every numbered theorem-like environment has exact Lean coverage. "
            "The classical Peter--Weyl upgrade appears only in unnumbered prose "
            "and is identified explicitly as an external theorem."
        ),
        "claims": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--tex", type=Path, default=REPO / "non_mf_groups_exist.tex"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=REPO / "metadata" / "NON_MF_NUMBERED_CLAIMS.json",
    )
    args = parser.parse_args()
    args.output.write_text(
        json.dumps(generate(args.tex), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"wrote {args.output} ({len(read_printed_claims(args.tex))} claims)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
