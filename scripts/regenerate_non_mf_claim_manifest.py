#!/usr/bin/env python3
r"""Regenerate the exact numbered-claim manifest from the manuscript boundary.

The manuscript is deliberately strict: every numbered theorem-like object has
exactly one ``\leanverified`` record, and that record names a wrapper with the
same outer proposition.  This generator records those pairs, statement hashes,
and explicit numbered-claim dependencies.  Semantic review remains necessary
when a wrapper or printed proposition changes; the generated diff makes that
review unavoidable and complete.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_non_mf_claim_manifest import read_printed_claims


REPO = Path(__file__).resolve().parent.parent


# Dependencies are part of the paper's statement-level proof graph.  They are
# intentionally explicit instead of inferred from prose or Lean imports.
DEPENDENCIES: dict[str, list[str]] = {
    "thm:kazhdan-clifford": ["prop:mf-equivalences", "thm:criterion",
                              "lem:square", "con:clifford"],
    "thm:A": ["def:E", "prop:mf-equivalences", "prop:maximal-cstar",
              "prop:literal-base-T", "prop:witness", "thm:criterion",
              "lem:unitarycorona", "lem:square"],
    "thm:C": ["thm:B", "con:clifford"],
    "thm:D": ["thm:A", "lem:faithfultrace"],
    "prop:mf-equivalences": ["lem:unitarycorona"],
    "prop:literal-base-T": ["def:E", "prop:p13-certificate"],
    "lem:linear": ["def:E"],
    "prop:witness": ["con:clifford", "lem:linear", "def:E"],
    "cor:notRFD": ["thm:B", "prop:witness"],
    "lem:unitarycorona": ["lem:lift"],
    "thm:criterion": ["def:pattern", "lem:compressorcollapse"],
    "lem:compressorcollapse": ["def:pattern"],
    "lem:portable": ["thm:A", "def:radical"],
    "prop:univquot": ["def:radical", "lem:lift", "lem:unitarycorona"],
    "cor:exactradical": ["def:radical"],
    "cor:nofaithful": ["thm:A"],
    "cor:quotclosure": ["thm:A"],
}


def generate(tex: Path) -> dict:
    entries = []
    for claim in read_printed_claims(tex):
        if len(claim.badges) != 1:
            raise SystemExit(
                f"{claim.claim_id}: expected exactly one exact badge, found "
                f"{len(claim.badges)}")
        role, module, declaration = claim.badges[0]
        if role != "exact":
            raise SystemExit(f"{claim.claim_id}: retained claims must be exact")
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
            "Every retained numbered theorem-like environment has one exact "
            "wrapper with the same outer proposition, no extra formal premise, "
            "and no paper-only mathematical input."),
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
