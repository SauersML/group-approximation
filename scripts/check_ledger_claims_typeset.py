#!/usr/bin/env python3
"""The Claim column of the step table is printed at readers, so it is TeX.

`tools/paper_site` typesets a step's claim with the same renderer it uses for
the manuscript, which means `$...$` for mathematics, `\\ref` for a numbered
result and `\\cite` for a source.  A cell written the way a table is written --
`C*_red(E)`, `x_n(x_n*x_n)^{-1/2}`, `‖x‖₂ ≤ ‖x‖`, a bare `thm:criterion`, a
word in capitals for emphasis, a `proof step:` prefix -- reaches the page as
itself.

Rows the page prints are a hard failure.  The rest are counted against a
baseline that may fall and may not rise, so a cell touched today is written
for a reader and the backlog drains rather than grows.
"""
import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEDGER = REPO / "metadata" / "NON_MF_PROOF_LEDGER.md"

# how many rows the page does not print are still written for the table; this
# may fall and may not rise
BACKLOG = 270

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
    ap.add_argument("--print-backlog", action="store_true",
                    help="report the current count and exit, to reset the baseline")
    args = ap.parse_args()

    printed, backlog = [], []
    for c in rows():
        if c[2].startswith("MOVED to"):
            continue                       # not a step; never reaches the page
        bad = faults(c[2])
        if not bad:
            continue
        (printed if c[5] != "EXACT" else backlog).append((c[0], c[1], bad, c[2]))

    for step, anchor, bad, cell in printed:
        print(f"{step} ({anchor}): {', '.join(bad)}\n    {cell[:110]}", file=sys.stderr)

    if args.print_backlog:
        print(len(backlog))
        return 0
    if printed:
        print(f"check-ledger-claims-typeset: {len(printed)} printed row(s) are not TeX",
              file=sys.stderr)
        return 1
    if len(backlog) > BACKLOG:
        print(f"check-ledger-claims-typeset: {len(backlog)} rows are not TeX, "
              f"baseline is {BACKLOG}; a row written for the table was added or edited",
              file=sys.stderr)
        return 1
    print(f"check-ledger-claims-typeset: every printed claim is TeX "
          f"({len(backlog)} unprinted rows still to convert, baseline {BACKLOG})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
