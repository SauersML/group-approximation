#!/usr/bin/env python3
"""Require every Lean docstring's claims *about the manuscript* to still be true.

Every other gate in this directory checks the mathematics.  `check_non_mf_refs`
checks that badges resolve, `check_non_mf_zero_input` checks where binders
print, `check_non_mf_claim_manifest` and the proof ledger check statements.
None of them reads a docstring.

That is a real hole, because a Lean module's docstring is where the module says
*what it corresponds to*: which remark it formalizes, what the manuscript
prints there, why a badge is or is not owed.  The theorem beside it stays true
while that prose rots, and nothing complains.  On 2026-08-16 a sweep found the
defect four times over, twice load-bearing:

* `Criterion/ClosedEnvelopeCompression`'s neighbourhood quoted a manuscript
  sentence -- "is the input the badge quantifies over rather than proves" --
  that occurs **zero** times in the `.tex`; the same fabricated quote had been
  copied into a gate's own roster and into the conditionality inventory, where
  it was the stated reason an item stayed open;
* `Analysis/CStarExactness` rested its "no badge is owed" argument on a
  manuscript sentence that had since been deleted;
* `Monsters/FournierFacioRealization` asserted that a companion module "was
  deleted the same day" when the file was present and tracked;
* `Sofic/AmalgamQuestionEndpoint` announced "NOT IN THE BUILD" while being
  root-imported.

## What this script checks

The manuscript may be split into a paper and companion notes.  Pass each
companion with `--companion-tex`; label and quotation checks use their union.

Two passes, both zero-judgement, both under `--strict`:

1. **Dangling manuscript references.**  Every `\\label{...}`, `\\ref{...}` and
   `\\eqref{...}` written inside a Lean file must name a label that exists in
   the manuscript.  A Lean file citing `\\ref{sec:proofA}` after that section
   was renamed is pointing at nothing, and no amount of reading the file
   reveals it.

2. **Line-number citations.**  A Lean docstring may not locate a passage by
   line number.  The manuscript is under continuous concurrent edit; a line
   number is stale the moment it is written, and unlike a dangling label it
   fails silently by pointing at the *wrong* passage rather than at none.  Cite
   a `\\label` or a distinctive string instead.

Neither pass can produce a false positive: a label either exists or it does
not, and a line number either appears or it does not.

## What this script deliberately does not check

Whether a quoted passage still matches the manuscript.  That needs a human,
because a paraphrase is legitimate and a stripped-down restatement in Lean
vocabulary is often clearer than the printed sentence.  `--quotes` runs the
heuristic and prints candidates for review; it never fails the build.

The heuristic that makes `--quotes` usable is the *framing filter*: only a
blockquote or `*"..."*` span whose preceding prose introduces it as a
manuscript quote is tested.  Without that filter the pass reports every
blockquote in the corpus, most of which are a module's own summary or a
quotation of an external source, and the signal is lost -- 41 candidates of
which 23 are noise, against 18 when framing is required.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
DEFAULT_LEAN = REPO / "GroupApproximation"

# `\label{...}`, `\ref{...}`, `\eqref{...}` as written inside a Lean docstring.
TEX_REF = re.compile(r"\\(?:label|ref|eqref)\{([^}\s]+)\}")

# "line 3964", "lines 3352--3374", "lines 1436–1438", "lines 177, 248", and the
# bare-`L` spelling "L1426–L1427", "(L1322–L1450)".
#
# The `L` alternative was added 2026-08-18.  The pass had been green on the
# whole corpus while four sites in `Monsters/P13SpectralGap.lean` and
# `Monsters/P13InvariantProjection.lean` located deleted sentences by
# `(L1426–L1427)`; the advisory `--quotes` pass printed them and the strict
# pass could not see them, which is the worst arrangement of the two.  Four
# digits minimum for that form, since `L2` and `L15` are ordinary identifiers
# in this corpus while a five-figure manuscript offset is not.
#
# Two digits minimum for the spelled-out form, so that "line 2 of the proof" is
# not a citation.
LINE_CITE = re.compile(
    r"\b(?:line|lines)\s+\d{2,6}(?:\s*(?:--|–|-|,|\s+to\s+)\s*\d{2,6})?"
    r"|\bL\d{4,6}(?:\s*(?:--|–|-)\s*L?\d{4,6})?",
    re.I,
)

# A citation whose target is a Lean file, not the manuscript: "that file's
# line 164", "`Sofic/Foo.lean` line 40".  Those drift too, but they are a
# different problem and this gate would only add noise by reporting them.
LEAN_TARGET = re.compile(r"(\.lean|that file's|this file's|module's)\s*[^.]{0,40}$",
                         re.I)

# Prose that introduces a quotation *of the manuscript*, as opposed to a
# module's own summary or a quotation of an external paper.
FRAMING = re.compile(
    r"(non_mf_groups_exist|manuscript|the paper|\\label\{|printed|prints|"
    r"reads:|says:|says of|asserts)",
    re.I,
)


def lean_files(root: Path) -> list[Path]:
    return sorted(root.rglob("*.lean"))


def tex_labels(tex: str) -> set[str]:
    return set(re.findall(r"\\label\{([^}]+)\}", tex))


def check_dangling(files: list[Path], labels: set[str]) -> list[str]:
    """Pass 1: a manuscript reference that names no label."""
    problems = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        for name in sorted(set(TEX_REF.findall(text))):
            if name not in labels:
                rel = path.relative_to(REPO)
                problems.append(
                    f"{rel}: references `{name}`, which is not a \\label in the "
                    "manuscript; cite a label that exists or drop the reference"
                )
    return problems


def check_line_citations(files: list[Path]) -> list[str]:
    """Pass 2: locating a manuscript passage by line number."""
    problems = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        if not FRAMING.search(text):
            # No manuscript talk at all; a "line 40" here is about something
            # else entirely.
            continue
        for match in LINE_CITE.finditer(text):
            # A Lean file may legitimately cite *another Lean file* by line --
            # those move too, but they are not a claim about the manuscript and
            # are not this gate's business.
            before = text[max(0, match.start() - 160):match.start()]
            if LEAN_TARGET.search(before):
                continue
            line_no = text.count("\n", 0, match.start()) + 1
            rel = path.relative_to(REPO)
            problems.append(
                f"{rel}:{line_no}: locates the manuscript by "
                f"`{' '.join(match.group(0).split())}`; line numbers drift under "
                "concurrent edit -- cite a \\label or a distinctive string"
            )
    return problems


def check_backtick_labels(files: list[Path], labels: set[str]) -> list[str]:
    """Advisory pass: a manuscript label cited in backticks rather than `\\ref`.

    `Theorem \\`thm:local\\`` is the same claim as `\\ref{thm:local}` and rots the
    same way, but pass 1 cannot see it.  This pass can -- and it is advisory
    rather than strict for a measured reason.

    Run over the whole corpus, it reports **212** dead tokens, and essentially
    all of them are correct references to the *nonsofic* paper, whose `.tex`
    is not in this checkout (`prop:match`, `cor:fgring`, `thm:allranks`, … are
    labels of that manuscript, cited from `Matching/` and `Endpoint/`).  A
    strict gate at that rate is a gate someone disables in a week.

    Restricting to files that name `non_mf_groups_exist.tex` cuts it to 16, of
    which several are still nonsofic labels in files that discuss both papers.
    So the honest form is advisory, and the reader adjudicates.  If the other
    manuscripts' sources ever land in the repo, feed their labels in and this
    can be promoted.
    """
    prefixes = sorted({name.split(":")[0] for name in labels if ":" in name})
    if not prefixes:
        return []
    pattern = re.compile(r"`(" + "|".join(prefixes) + r"):([A-Za-z0-9_.:-]+)`")
    notes = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        if "non_mf_groups_exist" not in text:
            continue
        for match in pattern.finditer(text):
            name = f"{match.group(1)}:{match.group(2)}"
            if name in labels:
                continue
            line_no = text.count("\n", 0, match.start()) + 1
            notes.append(f"{path.relative_to(REPO)}:{line_no}: `{name}`")
    return notes


def _plain_words(text: str) -> list[str]:
    """Prose words, with Lean and TeX notation stripped out."""
    text = re.sub(r"`[^`]*`", " ", text)
    text = re.sub(r"\$[^$]*\$", " ", text)
    text = re.sub(r"\\[a-zA-Z]+\{[^}]*\}", " ", text)
    text = re.sub(r"\\[a-zA-Z]+", " ", text)
    return re.findall(r"[A-Za-z][A-Za-z'-]+", text)


def check_quotes(files: list[Path], tex: str) -> list[str]:
    """Advisory pass: framed manuscript quotes with no overlap with the `.tex`.

    Reported, never fatal.  A run of six consecutive prose words is the test:
    shorter runs match by accident, and longer ones reject honest paraphrase.
    """
    haystack = " ".join(_plain_words(" ".join(tex.split()))).lower()
    notes = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        spans: list[tuple[int, str]] = []
        for match in re.finditer(r"(?:^> .*\n)+", text, re.M):
            body = " ".join(line[2:] for line in match.group(0).strip().split("\n"))
            spans.append((match.start(), " ".join(body.split())))
        for match in re.finditer(r'\*"(.+?)"\*', text, re.S):
            spans.append((match.start(), " ".join(match.group(1).split())))

        for start, quote in spans:
            if not FRAMING.search(text[max(0, start - 260):start]):
                continue
            words = [w.lower() for w in _plain_words(quote)]
            if len(words) < 6:
                continue
            if any(" ".join(words[i:i + 6]) in haystack
                   for i in range(len(words) - 5)):
                continue
            line_no = text.count("\n", 0, start) + 1
            rel = path.relative_to(REPO)
            notes.append(f"{rel}:{line_no}: {quote[:110]}")
    return notes


SELF_TEST_TEX = r"""
\section{Live}\label{sec:live}
\begin{lemma}\label{lem:live}
Every subgroup of an MF group is MF, by restriction of the embedding.
\end{lemma}
"""

# (filename, body, expected dangling, expected line-cite, expected quote note,
#  expected backtick note)
SELF_TEST_CASES: list[tuple[str, str, int, int, int, int]] = [
    ("Live.lean",
     "/-! `non_mf_groups_exist.tex`, \\ref{sec:live}: fine. -/\n",
     0, 0, 0, 0),
    ("Dangling.lean",
     "/-! `non_mf_groups_exist.tex`, \\ref{sec:gone}: dead. -/\n",
     1, 0, 0, 0),
    ("LineCite.lean",
     "/-! The manuscript prints this at lines 100--200. -/\n",
     0, 1, 0, 0),
    # The bare-`L` spelling of the same defect.  Both endpoints are one
    # citation, so this must report 1 and not 2.
    ("LineCiteBareL.lean",
     "/-! The manuscript prints this at (L1426-L1427). -/\n",
     0, 1, 0, 0),
    # Short `L` tokens are ordinary identifiers, not manuscript offsets.
    ("BareLIdentifier.lean",
     "/-! The manuscript's operator `L2` acts on the level `L15` block. -/\n",
     0, 0, 0, 0),
    # A line number whose target is another Lean file is not this gate's
    # business, even in a file that also talks about the manuscript.
    ("LeanTarget.lean",
     "/-! The manuscript says so; see `Foo.lean` line 164 for the interface. -/\n",
     0, 0, 0, 0),
    # No manuscript talk anywhere: a bare line number means something else.
    ("Unrelated.lean",
     "/-! See line 164 of the RFC. -/\n",
     0, 0, 0, 0),
    # A framed quote that really is in the manuscript.
    ("GoodQuote.lean",
     "/-! The manuscript reads:\n\n"
     "> Every subgroup of an MF group is MF, by restriction of the embedding.\n-/\n",
     0, 0, 0, 0),
    # A framed quote that is not.
    ("BadQuote.lean",
     "/-! The manuscript reads:\n\n"
     "> Every subgroup of a sofic group is finitely presented by descent.\n-/\n",
     0, 0, 1, 0),
    # An unframed blockquote is the module's own summary, not a quote.
    ("OwnSummary.lean",
     "/-! What this file proves:\n\n"
     "> Every subgroup of a sofic group is finitely presented by descent.\n-/\n",
     0, 0, 0, 0),
    # Backticked labels: dead one in a file that cites this manuscript.
    ("BacktickDead.lean",
     "/-! `non_mf_groups_exist.tex`, Lemma `lem:gone`. -/\n",
     0, 0, 0, 1),
    ("BacktickLive.lean",
     "/-! `non_mf_groups_exist.tex`, Lemma `lem:live`. -/\n",
     0, 0, 0, 0),
    # A dead backticked label in a file that never names this manuscript is a
    # label of another paper, and must not be reported.
    ("BacktickOtherPaper.lean",
     "/-! Proposition `prop:match` of the nonsofic paper. -/\n",
     0, 0, 0, 0),
]


def self_test() -> int:
    """Each pass, against a synthetic tree with known answers."""
    global REPO
    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        saved, REPO = REPO, root
        try:
            labels = tex_labels(SELF_TEST_TEX)
            for name, body, want_dangle, want_line, want_quote, want_tick in \
                    SELF_TEST_CASES:
                path = root / name
                path.write_text(body, encoding="utf-8")
                got = (
                    len(check_dangling([path], labels)),
                    len(check_line_citations([path])),
                    len(check_quotes([path], SELF_TEST_TEX)),
                    len(check_backtick_labels([path], labels)),
                )
                want = (want_dangle, want_line, want_quote, want_tick)
                if got != want:
                    failures.append(f"{name}: expected {want}, got {got}")
                path.unlink()
        finally:
            REPO = saved

    if failures:
        print("check-manuscript-claims: self-test FAILED:")
        for failure in failures:
            print(f"  {failure}")
        return 1
    print(f"check-manuscript-claims: self-test passed "
          f"({len(SELF_TEST_CASES)} cases)")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument(
        "--companion-tex", type=Path, action="append", default=[],
        help="add labels and prose from a companion TeX edition")
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--strict", action="store_true",
                        help="exit nonzero on any pass-1 or pass-2 problem")
    parser.add_argument("--quotes", action="store_true",
                        help="also run the advisory framed-quote heuristic")
    parser.add_argument("--self-test", action="store_true",
                        help="check each pass against known answers and exit")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    tex_paths = [args.tex, *args.companion_tex]
    tex = "\n".join(path.read_text(encoding="utf-8") for path in tex_paths)
    labels = tex_labels(tex)
    files = lean_files(args.lean)

    problems = check_dangling(files, labels) + check_line_citations(files)

    if problems:
        print(f"check-manuscript-claims: {len(problems)} problem(s):")
        for problem in problems:
            print(f"  {problem}")
    else:
        print(f"check-manuscript-claims: {len(files)} modules, "
              f"{len(labels)} labels; no dangling references, "
              "no line-number citations")

    if args.quotes:
        backticked = check_backtick_labels(files, labels)
        print(f"\ncheck-manuscript-claims: {len(backticked)} backticked label(s) "
              "naming no \\label, in files that cite this manuscript (advisory; "
              "a label of another paper is not a defect):")
        for note in backticked:
            print(f"  {note}")

        notes = check_quotes(files, tex)
        print(f"\ncheck-manuscript-claims: {len(notes)} framed quote(s) with no "
              "six-word overlap with the manuscript (advisory; a paraphrase is "
              "not a defect):")
        for note in notes:
            print(f"  {note}")

    return 1 if (problems and args.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
