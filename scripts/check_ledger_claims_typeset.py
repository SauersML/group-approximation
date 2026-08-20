#!/usr/bin/env python3
"""The Claim column of the step table is printed at readers, so it is TeX.

`tools/paper_site` typesets a step's claim with the same renderer it uses for
the manuscript, which means `$...$` for mathematics, `\\ref` for a numbered
result and `\\cite` for a source.  A cell written the way a table is written --
`C*_red(E)`, `x_n(x_n*x_n)^{-1/2}`, `‖x‖₂ ≤ ‖x‖`, a bare `thm:criterion`, a
word in capitals for emphasis, a `proof step:` prefix -- reaches the page as
itself.

Every row is a hard failure.  A row graded EXACT today can be downgraded
tomorrow, and then its cell is what a reader sees, so there is no row this
may be relaxed for.
"""
import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEDGER = REPO / "metadata" / "NON_MF_PROOF_LEDGER.md"

MATH_CHARS = "‖⟨⟩→←↦≤≥≠∈∉⊆⊇⊗⊕∘∀∃±∓·×⋊⋉≅≃≈∗†√∞∏∑αβγδεζηθκλμνξπρστφχψωΓΔΘΛΞΠΣΦΨΩ₀₁₂₃₄₅₆₇₈₉ℂℕℚℝℤ𝒩𝒬"

FAULTS = [
    ("mathematics outside math mode", re.compile("[" + MATH_CHARS + "]")),
    ("ASCII mathematics", re.compile(r"\b[A-Za-z]_[A-Za-z0-9(){]|\^\{|\*_|C\*|\bM_")),
    ("a label where a number belongs", re.compile(r"\b(?:thm|lem|prop|cor|def|rem|eq|sec|fig|p):[a-zA-Z0-9-]+")),
    ("capitals for emphasis", re.compile(r"\b[A-Z]{4,}\b")),
    ("a prefix meant for the table", re.compile(r"^\s*(?:proof step|statement|step)\s*:", re.I)),
]

# a cell is scanned outside its math; what is inside $...$ is TeX already
MATH_SPAN = re.compile(r"\$[^$]*\$")


def faults(cell):
    outside = MATH_SPAN.sub(" ", cell)
    # \textup{(T)}, \ref{...}, \cite{...} and friends are TeX, not label leaks
    outside = re.sub(r"\\[a-zA-Z]+\{[^{}]*\}", " ", outside)
    return [name for name, rx in FAULTS if rx.search(outside)]


def rows():
    txt = LEDGER.read_text(encoding="utf-8")
    m = re.search(r"<!-- LEDGER-STEPS -->(.*?)<!-- END-LEDGER-STEPS -->", txt, re.S)
    if not m:
        sys.exit("no step table in " + str(LEDGER))
    for line in m.group(1).splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 6 or cells[0] in ("Step", "") or set(cells[0]) <= set("- "):
            continue
        yield cells


def main():
    ap = argparse.ArgumentParser()
    ap.parse_args()

    bad = []
    total = [0]
    for c in rows():
        if c[2].startswith("MOVED to"):
            continue                       # not a step; never reaches the page
        found = faults(c[2])
        if found:
            bad.append((c[0], c[1], found, c[2]))
        total[0] += 1

    for step, anchor, found, cell in bad:
        print(f"{step} ({anchor}): {', '.join(found)}\n    {cell[:110]}", file=sys.stderr)
    if bad:
        print(f"check-ledger-claims-typeset: {len(bad)} of {total[0]} claims are not TeX",
              file=sys.stderr)
        return 1
    print(f"check-ledger-claims-typeset: all {total[0]} claims are TeX")
    return 0


if __name__ == "__main__":
    sys.exit(main())
