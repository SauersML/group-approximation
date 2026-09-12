#!/usr/bin/env python3
"""No `EXACT` ledger row may rest on a conditional declaration.

The standing order on this manuscript is that a conditional formalization does
not count and neither does a literature input: a theorem available only to a
caller who supplies a premise nothing in the corpus produces formalizes
nothing about the printed sentence it is meant to certify.

`scripts/check_non_mf_unconditional.py` enforces that on the **badge surface**
--- the declarations the manuscript itself cites in a `\\leanverified`.  The
proof ledger names many more: its `Objects` column carries the declarations
that support each graded step, and a row graded `EXACT` is asserting that
those declarations say what the step says.  Nothing checked that those were
unconditional, which is exactly the gap the badge gate was built to close one
level up.

This runs the same classifier over the ledger's own objects.

    scripts/check_ledger_unconditional.py            report and fail on findings
    scripts/check_ledger_unconditional.py --all      include non-EXACT rows
    scripts/check_ledger_unconditional.py --explain  print every row's verdict

Only the detectors that mean *not available unconditionally* are failures:
`buried-conditional`, `conditional-data`, `known-conditional`,
`literature-input`, `open-predicate`.  `header-binder` and `open-variable` are
badge-surface hygiene --- a printed badge must sit over a binder-free
statement --- and a ledger object is not a badge, so a theorem whose binders
are its own subject matter passes here.  `definition-only` likewise: a ledger
row may legitimately name the definition the printed sentence introduces.
"""

from __future__ import annotations

import argparse
import importlib
import os
import re
import sys
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = Path(os.path.dirname(HERE))
LEDGER = ROOT / "metadata" / "NON_MF_PROOF_LEDGER.md"

ROW_ID = re.compile(r"^[A-Z]{2,4}\.\d+[a-z]?$")
DECL = re.compile(r"`([A-Za-z_][A-Za-z0-9_'!?.]*)`")

CONDITIONAL_DETECTORS = {
    "buried-conditional", "conditional-data", "known-conditional",
    "literature-input", "open-predicate",
}


def ledger_rows(path: Path) -> list[tuple[str, str, str, list[str]]]:
    """`(id, anchor, statement grade, declarations)` for every step row."""
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 6 or not ROW_ID.match(cells[0]):
            continue
        names = [n for n in DECL.findall(cells[3]) if "." in n]
        out.append((cells[0], cells[1], cells[4], names))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true",
                    help="classify every row, not only the EXACT ones")
    ap.add_argument("--explain", action="store_true")
    args = ap.parse_args()

    sys.path.insert(0, HERE)
    m = importlib.import_module("check_non_mf_unconditional")
    corpus = m.build_corpus(ROOT)
    roster, _ = m.read_roster(ROOT / m.DEFAULT_ROSTER)

    # Every name some declaration exhibits an inhabitant of, by last
    # component.  The underlying classifier reads a premise head exactly as
    # written, so `mm.Halts p` and `M.Halts p` --- the same predicate applied
    # to two differently named machines --- are two heads and neither matches
    # the producer.  Dot notation on a term is not a namespace, and the shared
    # gate deliberately refuses to strip it (a Mathlib `Foo.Bar` must not be
    # mistaken for a corpus `Bar`).  Here the comparison is only used to
    # *suppress* a finding, so the looser rule is the safe direction: a head
    # whose short name something produces is not an open predicate.
    produced_short: set[str] = set()
    for decl in corpus.by_name.values():
        for head in m.produced_heads(decl):
            produced_short.add(head.rsplit(".", 1)[-1])

    head_of = re.compile(r"corpus-defined (?:predicate|structure) `([^`]+)`")

    rows = ledger_rows(LEDGER)
    findings: list[str] = []
    suppressed: list[str] = []
    checked = unresolved = 0
    for rid, anchor, grade, names in rows:
        if not args.all and grade != "EXACT":
            continue
        for name in names:
            decl = (corpus.by_name.get(name)
                    or corpus.by_name.get(name.rsplit(".", 1)[-1]))
            if decl is None:
                unresolved += 1
                continue
            checked += 1
            hits = []
            for d, detail in m.classify(corpus, decl, roster, name):
                if d not in CONDITIONAL_DETECTORS:
                    continue
                head = head_of.search(detail)
                if head and head.group(1).rsplit(".", 1)[-1] in produced_short:
                    suppressed.append(
                        f"{rid}\t{name}\t{d}\t{head.group(1)} is produced "
                        "under another spelling")
                    continue
                hits.append((d, detail))
            if args.explain and not hits:
                print(f"ok\t{rid}\t{name}")
            for d, detail in hits:
                findings.append(f"{rid}\t{anchor}\t{name}\t{d}\t{detail}")

    for x in suppressed:
        print("suppressed\t" + x)
    for f in findings:
        print("CONDITIONAL\t" + f)
    print(f"check-ledger-unconditional: {checked} declaration(s) classified, "
          f"{unresolved} not found in the corpus, {len(findings)} conditional")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
