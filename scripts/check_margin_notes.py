#!/usr/bin/env python3
"""Check that every Lean margin note lands where it belongs.

The manuscripts set their Lean certificates with ``\\leanverified``, which
puts a margin note beside the line that carries the badge.  LaTeX protects
notes from each other by pushing a colliding note down the margin, and the
PDF workflows already fail on the resulting ``Marginpar ... moved`` warning.
Nothing warns about the other two ways a note can go wrong: it can hang off
the foot of the page when it is anchored low and its declaration list is
long, and it can drift so far from its anchor that it appears to certify the
wrong statement.

This checker measures the notes in the shipped page.  It compiles an
instrumented twin of the manuscript in which each note records its own
position, its height and the position of the line it is attached to -- all
through ``\\pdfsavepos`` whatsits, which occupy no space, so the twin has the
same layout as the manuscript itself.  It then reports overlapping notes,
notes reaching into the trim margin, notes displaced from their anchor line,
and notes whose anchor is on another page.

A failure is fixed in the manuscript, not here: merge badges that sit closer
together than one note is tall (adjacent badges coalesce into one note), or
move a badge to an earlier line of the statement it certifies, which is
where a tall note wants to hang from.

Requires lualatex; run it on a machine with TeX Live, not on a laptop.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SP = 65536.0                      # scaled points per point
PAPER_WIDTH = 614.295             # letterpaper, in points
PAPER_HEIGHT = 794.9694
SAFE_BAND = 36.0                  # required clear band at every paper edge
ANCHOR_DRIFT = 6.0                # a note may sit this far below its anchor

# The probe: definitions, then the three call sites inside the note macros.
PROBE = r"""\ifdefined\pdfsavepos\else
  \let\pdfsavepos\savepos
  \let\pdflastxpos\lastxpos
  \let\pdflastypos\lastypos
\fi
\newwrite\lean@posout
\immediate\openout\lean@posout=\jobname.leanpos\relax
\newcount\lean@id
\def\lean@posmark{%
  \global\advance\lean@id\@ne
  \leavevmode\pdfsavepos
  \begingroup
    \edef\@tempa{\endgroup
      \noexpand\write\lean@posout{POS \the\lean@id\space
        \noexpand\the\noexpand\pdflastxpos\space
        \noexpand\the\noexpand\pdflastypos\space \noexpand\thepage}}%
  \@tempa}
\def\lean@dimmark{%
  \immediate\write\lean@posout{DIM \the\lean@id\space
    \the\lean@ht\space\the\lean@dp}}
\def\lean@ancmark{%
  \pdfsavepos
  \write\lean@posout{ANC \the\pdflastxpos\space\the\pdflastypos\space\thepage}}
"""

INSTRUMENTATION = (
    ("\\def\\lean@build#1{%", PROBE + "\\def\\lean@build#1{%"),
    ("\\selectfont\\scshape Lean\\par}",
     "\\selectfont\\scshape\\lean@posmark Lean\\par}"),
    ("  \\lean@ht\\ht\\lean@bx \\lean@dp\\dp\\lean@bx}",
     "  \\lean@ht\\ht\\lean@bx \\lean@dp\\dp\\lean@bx\n  \\lean@dimmark}"),
    ("  \\marginpar[\\lean@inner]", "  \\lean@ancmark\n  \\marginpar[\\lean@inner]"),
)

LOG_COMPLAINT = re.compile(r"Marginpar on page \S+ moved|[Ll]ost marginpar")


@dataclass
class Note:
    rank: int
    page: str
    x: float
    baseline: float
    top: float
    bottom: float
    anchor: float | None = None
    anchor_page: str | None = None

    @property
    def height(self) -> float:
        return self.top - self.bottom


def instrument(source: str) -> str:
    """Return the manuscript with position tracing added to its note macros."""
    for old, new in INSTRUMENTATION:
        if source.count(old) != 1:
            raise SystemExit(
                "this manuscript does not carry the margin-note macros this "
                f"checker instruments (looking for {old.strip()!r}); if the "
                "macros were rewritten, update INSTRUMENTATION here as well"
            )
        source = source.replace(old, new)
    return source


def parse_positions(trace: str) -> list[Note]:
    """Join the shipped-note records of one LaTeX run into placed notes."""
    positions: dict[int, tuple[float, float, str]] = {}
    sizes: dict[int, tuple[float, float]] = {}
    anchors: list[tuple[float, str]] = []
    for line in trace.splitlines():
        field = line.split()
        if not field:
            continue
        if field[0] == "POS":
            positions[int(field[1])] = (int(field[2]) / SP, int(field[3]) / SP,
                                        field[4])
        elif field[0] == "DIM":
            sizes[int(field[1])] = (float(field[2].rstrip("pt")),
                                    float(field[3].rstrip("pt")))
        elif field[0] == "ANC":
            anchors.append((int(field[2]) / SP, field[3]))
    notes: list[Note] = []
    # A note builds two boxes, one per margin; only the one the output routine
    # keeps ever reaches a page, so only it writes a POS record.
    for rank, identifier in enumerate(sorted(positions), start=1):
        x, baseline, page = positions[identifier]
        height, depth = sizes[identifier]
        notes.append(Note(rank=rank, page=page, x=x, baseline=baseline,
                          top=baseline + height, bottom=baseline - depth))
    if len(anchors) == len(notes):
        for note, (anchor, page) in zip(notes, anchors):
            note.anchor, note.anchor_page = anchor, page
    return notes


def inspect(notes: list[Note], safe_band: float = SAFE_BAND,
            drift: float = ANCHOR_DRIFT) -> list[str]:
    problems: list[str] = []
    for note in notes:
        if note.bottom < safe_band:
            problems.append(
                f"page {note.page}: note {note.rank} reaches to {note.bottom:.1f}pt "
                f"above the foot of the sheet, inside the {safe_band:.0f}pt trim "
                "band; anchor it on an earlier line of its statement"
            )
        if note.top > PAPER_HEIGHT - safe_band:
            problems.append(
                f"page {note.page}: note {note.rank} starts at {note.top:.1f}pt, "
                "inside the head trim band"
            )
        if not safe_band < note.x < PAPER_WIDTH - safe_band:
            problems.append(
                f"page {note.page}: note {note.rank} sits at x={note.x:.1f}pt, "
                "outside the printable width"
            )
        if note.anchor is None:
            continue
        if note.anchor_page != note.page:
            problems.append(
                f"page {note.page}: note {note.rank} is anchored on page "
                f"{note.anchor_page}, so it certifies a statement the reader "
                "cannot see"
            )
        elif note.anchor - note.baseline > drift:
            problems.append(
                f"page {note.page}: note {note.rank} sits "
                f"{note.anchor - note.baseline:.1f}pt below the line it certifies; "
                "merge it with the badge above or move that badge"
            )
    by_page: dict[str, list[Note]] = {}
    for note in notes:
        by_page.setdefault(note.page, []).append(note)
    for page, page_notes in by_page.items():
        page_notes.sort(key=lambda n: -n.top)
        for upper, lower in zip(page_notes, page_notes[1:]):
            if lower.top > upper.bottom:
                problems.append(
                    f"page {page}: notes {upper.rank} and {lower.rank} overlap by "
                    f"{lower.top - upper.bottom:.1f}pt"
                )
    return problems


def build(tex: Path, workdir: Path) -> tuple[str, str]:
    """Compile the instrumented twin; return its trace and its log."""
    workdir.mkdir(parents=True, exist_ok=True)
    twin = workdir / f"{tex.stem}-margincheck.tex"
    twin.write_text(instrument(tex.read_text(encoding="utf-8")), encoding="utf-8")
    if shutil.which("latexmk") is None:
        raise SystemExit("latexmk is not on PATH; run this where TeX Live lives")
    subprocess.run(
        ["latexmk", "-lualatex", "-interaction=nonstopmode", "-file-line-error",
         twin.name],
        cwd=workdir, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        check=False,
    )
    trace = twin.with_suffix(".leanpos")
    log = twin.with_suffix(".log")
    if not trace.is_file():
        raise SystemExit(
            f"no position trace was written; read {log} for the LaTeX failure"
        )
    return trace.read_text(encoding="utf-8"), log.read_text(
        encoding="utf-8", errors="replace")


def self_test() -> int:
    good = [Note(1, "3", 500.0, 600.0, 604.0, 570.0, anchor=604.0, anchor_page="3"),
            Note(2, "3", 500.0, 400.0, 404.0, 380.0, anchor=404.0, anchor_page="3")]
    assert inspect(good) == [], inspect(good)
    overlap = [Note(1, "3", 500.0, 600.0, 604.0, 400.0, anchor=604.0, anchor_page="3"),
               Note(2, "3", 500.0, 420.0, 424.0, 380.0, anchor=424.0, anchor_page="3")]
    assert any("overlap" in p for p in inspect(overlap))
    falls_off = [Note(1, "3", 500.0, 60.0, 64.0, -6.0, anchor=64.0, anchor_page="3")]
    assert any("foot of the sheet" in p for p in inspect(falls_off))
    pushed = [Note(1, "3", 500.0, 600.0, 604.0, 570.0, anchor=640.0, anchor_page="3")]
    assert any("below the line it certifies" in p for p in inspect(pushed))
    stranded = [Note(1, "4", 500.0, 600.0, 604.0, 570.0, anchor=604.0, anchor_page="3")]
    assert any("anchored on page" in p for p in inspect(stranded))
    parsed = parse_positions(
        "DIM 1 4.0pt 30.0pt\nDIM 2 4.0pt 30.0pt\n"
        "ANC 32000000 40000000 7\nPOS 1 32000000 39000000 7\n")
    assert len(parsed) == 1 and parsed[0].page == "7", parsed
    assert abs(parsed[0].height - 34.0) < 1e-6, parsed[0].height
    print("check-margin-notes: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tex", type=Path,
                        default=REPO / "non_mf_groups_exist.tex")
    parser.add_argument("--workdir", type=Path, default=REPO / "build" / "margincheck")
    parser.add_argument("--safe-band", type=float, default=SAFE_BAND,
                        help="clear band required at each paper edge, in points")
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    if arguments.self_test:
        return self_test()
    if not arguments.tex.is_file():
        raise SystemExit(f"no such manuscript: {arguments.tex}")
    trace, log = build(arguments.tex, arguments.workdir)
    notes = parse_positions(trace)
    if not notes:
        raise SystemExit("the manuscript placed no margin notes at all")
    problems = inspect(notes, arguments.safe_band)
    problems += [f"LaTeX moved a note: {line.strip()}"
                 for line in log.splitlines() if LOG_COMPLAINT.search(line)]
    heights = sorted(note.height for note in notes)
    print(f"check-margin-notes: {len(notes)} notes on "
          f"{len({note.page for note in notes})} pages; tallest "
          f"{heights[-1]:.1f}pt, median {heights[len(heights) // 2]:.1f}pt; "
          f"lowest foot {min(note.bottom for note in notes):.1f}pt")
    if problems:
        print(f"check-margin-notes: {len(problems)} problem(s):")
        for problem in problems:
            print(f"  {problem}")
        return 1
    print("check-margin-notes: every note sits beside the line it certifies")
    return 0


if __name__ == "__main__":
    sys.exit(main())
