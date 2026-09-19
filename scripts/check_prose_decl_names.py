#!/usr/bin/env python3
"""Resolve declaration names quoted in prose against the declarations that exist.

Two gates already resolve *references* against reality.  `check_non_mf_refs.py`
resolves every `\\leanverified` badge in the manuscript;
`check_manuscript_claims.py` resolves every `\\label` a Lean docstring cites.  Nothing resolves the other direction: a **declaration name**
written in prose -- inside a Lean docstring, or inside a note in
`metadata/NON_MF_PROOF_LEDGER.md` -- is unchecked, in both of the ways it can be
wrong.

On 2026-08-18 both ways were found in quantity, which is why this exists.

* **A name that does not resolve.**  `Sofic/MarkedCompressionRootCapture`'s
  docstring recommended `KazhdanAsymptoticCommutant.compressionDefect_hsDistSq_vanishing_literal`
  as the alternative to its Appendix-B step.  That name occurred nowhere else in
  the corpus, and could not have: the module that would have to contain it is an
  *import* of the file naming it, so the import direction forbade it.  Separately,
  `Analysis/VectorOmegaAction`'s own header listed nine declarations under names
  the file does not use, one of them (`norm_actOmega_le`) naming a fact the file
  did not prove at all.
* **A name asserted absent that resolves.**  Harder to see and worth more.
  Ledger row `KT.05` said "no `CompleteSpace` instance is claimed" while
  `OmegaHilbertComplete.kOmegaCompleteSpace` was in the root closure compiling;
  `PRE.07` said "the trace bound has no located declaration" while
  `PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm` was; the findings
  section said what is absent is "any ultraproduct along a genuine free `ω`"
  while `OmegaWeightedAmbient.omega_route_kazhdan_transport` proved Theorem 3.1
  through one.  Every such row was held on a fact that had expired.

This script reports the first kind, which is mechanical.  The second kind cannot
be detected from the text alone -- "no declaration does X" names no declaration
to resolve -- but the first is a good proxy: a note that has drifted far enough
to name a dead declaration has usually drifted far enough to be wrong about what
exists.

## Why it reports rather than fails

It is deliberately **not** wired into `scripts/check.py`'s verdict.  The corpus
has never been checked this way, the true violation count is unknown until it
runs, and a new gate that turns an unknown number of pre-existing prose defects
into a red build would block every lane for something no commit introduced.
Run it, fix what it finds, and only then decide whether it should fail.

## The heuristic, and why it is this one

Most backticked text in these docstrings is not a declaration name: it is
mathematics, tactic names, mathlib lemmas, file paths, English.  Flagging every
unresolvable dotted token would drown the signal in mathlib references.

So a candidate is reported only when **some proper prefix of it is a namespace
this development actually declares into**, and the full name is not a
declaration, not a module, and not itself a namespace.  The last two filters are
not fastidiousness: without them the first run reported 31 hits of which 29 were
prose correctly cross-referencing a module or a namespace.  That is exactly the shape of the failure: the right namespace, the
wrong or absent name.  A mathlib name has no repo namespace as a prefix and is
skipped; a name in a repo namespace that resolves is skipped; a name in a repo
namespace that does not resolve is the thing worth reading.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import build_index

REPO = Path(__file__).resolve().parent.parent

# A backticked token that could be a dotted Lean name: at least one dot, and
# only identifier characters around the dots.  Lean identifiers admit Unicode
# letters, digits, `_`, `'`, `!`, `?`; the character class below is deliberately
# permissive on letters and strict on everything else.
CANDIDATE = re.compile(r"`([^`\s]+)`")
DOTTED = re.compile(r"^[A-Za-z_][^\s]*(\.[^\s.]+)+$")
# Tokens that are paths, not names.
PATHISH = re.compile(r"[/\\]|\.lean$|\.md$|\.tex$|\.py$")

DOCSTRING = re.compile(r"/-[-!](.*?)-/", re.S)


def repo_namespaces(index: dict[str, Path]) -> set[str]:
    """Every proper prefix of a declared name, i.e. every namespace declared into."""
    spaces: set[str] = set()
    for name in index:
        parts = name.split(".")
        for i in range(1, len(parts)):
            spaces.add(".".join(parts[:i]))
    return spaces


def candidates(text: str) -> list[str]:
    out = []
    for tok in CANDIDATE.findall(text):
        tok = tok.strip()
        if not DOTTED.match(tok):
            continue
        if PATHISH.search(tok):
            continue
        out.append(tok)
    return out


def module_names(repo: Path) -> set[str]:
    """Every module in the development, as a dotted name.

    Prose cross-references modules constantly -- "see
    `GroupApproximation.Sofic.SoficEnvelopeExistence`" -- and a module is not a
    declaration, so it is absent from the index and would otherwise be reported.
    On the first run this was 29 of 31 hits: the heuristic without this filter
    measures cross-references, not defects.
    """
    names: set[str] = set()
    root = repo / "GroupApproximation"
    if root.exists():
        for path in root.rglob("*.lean"):
            rel = path.relative_to(repo).with_suffix("")
            names.add(".".join(rel.parts))
    if (repo / "GroupApproximation.lean").exists():
        names.add("GroupApproximation")
    return names


def check_text(label: str, text: str, index: dict[str, Path],
               spaces: set[str], modules: set[str]) -> list[tuple[str, str]]:
    findings = []
    for tok in candidates(text):
        if tok in index:
            continue
        if tok in modules:
            continue
        # A namespace is not a declaration either, and prose names namespaces
        # as freely as it names modules.  On the first two runs this and the
        # module filter together accounted for 29 of 31 hits.
        if tok in spaces:
            continue
        # Also accept a name written without its root namespace.
        if any(full.endswith("." + tok) for full in index):
            continue
        parts = tok.split(".")
        if not any(".".join(parts[:i]) in spaces for i in range(1, len(parts))):
            continue
        findings.append((label, tok))
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, default=REPO)
    ap.add_argument("--quiet", action="store_true",
                    help="print only the counts")
    args = ap.parse_args()

    index = build_index(args.repo)
    spaces = repo_namespaces(index)
    modules = module_names(args.repo)

    findings: list[tuple[str, str]] = []

    lean_root = args.repo / "GroupApproximation"
    for path in sorted(lean_root.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        rel = str(path.relative_to(args.repo))
        for doc in DOCSTRING.findall(text):
            findings.extend(check_text(rel, doc, index, spaces, modules))

    ledger = args.repo / "metadata" / "NON_MF_PROOF_LEDGER.md"
    if ledger.exists():
        findings.extend(
            check_text("metadata/NON_MF_PROOF_LEDGER.md",
                       ledger.read_text(encoding="utf-8"), index, spaces,
                       modules))

    by_place: dict[str, list[str]] = {}
    for place, tok in findings:
        by_place.setdefault(place, []).append(tok)

    if not args.quiet:
        for place in sorted(by_place):
            for tok in sorted(set(by_place[place])):
                print(f"{place}: prose names `{tok}`, which does not resolve")

    total = len({(p, t) for p, t in findings})
    print(f"check-prose-decl-names: {len(index)} declarations indexed, "
          f"{total} unresolvable name(s) quoted in prose across "
          f"{len(by_place)} file(s)")
    # Report-only by design; see the module docstring.
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
