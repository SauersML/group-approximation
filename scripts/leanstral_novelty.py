#!/usr/bin/env python3
"""Select a Leanstral target that no previous autonomous run has reserved.

A target is a (Lean source path, declaration anchor) pair. Reservations live
outside main, on the automation/leanstral-state branch, so they survive failed
runs and unmerged/closed PRs without polluting the research history.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import tempfile

DECL_RE = re.compile(
    r"^\s*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)

PRIORITY_DIRS = {
    "Sofic": 100,
    "PropertyTT": 95,
    "PropertyT": 90,
    "Endpoint": 88,
    "KOne": 86,
    "Analysis": 78,
    "Algebra": 74,
    "Kazhdan": 72,
    "Criterion": 70,
}
NAME_BONUSES = {
    "PaperStatements": 55,
    "Manuscript": 50,
    "Endpoint": 45,
    "Construction": 25,
    "Obstruction": 25,
    "Rigidity": 20,
    "Approximation": 20,
}


@dataclass(frozen=True)
class Candidate:
    path: str
    anchor: str
    line: int
    score: int


def parse_reservations(path: Path) -> tuple[set[tuple[str, str]], set[str]]:
    reserved: set[tuple[str, str]] = set()
    run_ids: set[str] = set()
    if not path.is_file():
        return reserved, run_ids
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw.strip() or raw.startswith("#"):
            continue
        parts = raw.split("\t")
        if len(parts) < 4:
            continue
        run_id, _timestamp, lean_path, anchor = parts[:4]
        run_ids.add(run_id)
        reserved.add((lean_path, anchor))
    return reserved, run_ids


def parse_bootstrap_blocks(path: Path) -> set[str]:
    if not path.is_file():
        return set()
    return {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }


def focus_terms(focus: str) -> list[str]:
    return [
        term.lower()
        for term in re.findall(r"[A-Za-z0-9_]{3,}", focus)
        if term.lower() not in {"theorem", "lemma", "prove", "proof", "lean"}
    ]


def score_candidate(path: Path, anchor: str, content: str, focus: str) -> int:
    score = 0
    parts = set(path.parts)
    for directory, points in PRIORITY_DIRS.items():
        if directory in parts:
            score += points

    context = path.as_posix() + " " + anchor
    for marker, points in NAME_BONUSES.items():
        if marker.lower() in context.lower():
            score += points

    for term in focus_terms(focus):
        if term in anchor.lower():
            score += 1200
        elif term in context.lower():
            score += 700
        elif term in content.lower():
            score += 120

    if re.search(rf"^\s*(?:theorem|lemma)\s+{re.escape(anchor)}\b", content, re.M):
        score += 20
    return score


def enumerate_candidates(
    root: Path,
    reserved: set[tuple[str, str]],
    bootstrap_blocked_paths: set[str],
    focus: str,
) -> list[Candidate]:
    candidates: list[Candidate] = []
    base = root / "GroupApproximation"
    for path in sorted(base.rglob("*.lean")):
        relative = path.relative_to(root).as_posix()
        if relative in bootstrap_blocked_paths:
            continue
        content = path.read_text(encoding="utf-8")
        for line_number, line in enumerate(content.splitlines(), 1):
            match = DECL_RE.match(line)
            if not match:
                continue
            anchor = match.group(1)
            if (relative, anchor) in reserved:
                continue
            candidates.append(
                Candidate(
                    path=relative,
                    anchor=anchor,
                    line=line_number,
                    score=score_candidate(
                        path.relative_to(root), anchor, content, focus
                    ),
                )
            )
    candidates.sort(key=lambda c: (-c.score, c.path, c.line, c.anchor))
    return candidates


def select(root: Path, ledger: Path, bootstrap: Path, focus: str) -> Candidate | None:
    reserved, _ = parse_reservations(ledger)
    blocked_paths = parse_bootstrap_blocks(bootstrap)
    candidates = enumerate_candidates(root, reserved, blocked_paths, focus)
    return candidates[0] if candidates else None


def self_test() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        (root / "GroupApproximation" / "Sofic").mkdir(parents=True)
        (root / "GroupApproximation" / "PropertyTT").mkdir(parents=True)
        (root / "GroupApproximation" / "Sofic" / "A.lean").write_text(
            "theorem alpha : True := by trivial\n"
            "lemma beta : True := by trivial\n",
            encoding="utf-8",
        )
        (root / "GroupApproximation" / "PropertyTT" / "B.lean").write_text(
            "theorem gamma : True := by trivial\n",
            encoding="utf-8",
        )
        ledger = root / "ledger.tsv"
        bootstrap = root / "bootstrap.txt"

        candidate = select(root, ledger, bootstrap, "gamma")
        assert candidate and candidate.anchor == "gamma"

        ledger.write_text(
            "100\t2026-01-01T00:00:00Z\t"
            "GroupApproximation/PropertyTT/B.lean\tgamma\n",
            encoding="utf-8",
        )
        candidate = select(root, ledger, bootstrap, "gamma")
        assert candidate and candidate.anchor != "gamma"

        bootstrap.write_text(
            "GroupApproximation/Sofic/A.lean\n", encoding="utf-8"
        )
        candidate = select(root, ledger, bootstrap, "")
        assert candidate is None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--ledger", type=Path)
    parser.add_argument("--bootstrap-blocked", type=Path)
    parser.add_argument("--focus", default="")
    parser.add_argument("--github-output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        print("leanstral novelty selector self-test: ok")
        return

    if args.ledger is None or args.bootstrap_blocked is None:
        parser.error("--ledger and --bootstrap-blocked are required")

    candidate = select(args.root, args.ledger, args.bootstrap_blocked, args.focus)
    if candidate is None:
        print("No unreserved Lean declaration anchors remain.")
        if args.github_output:
            with args.github_output.open("a", encoding="utf-8") as output:
                output.write("found=false\n")
        return

    print(
        f"selected {candidate.path} :: {candidate.anchor} "
        f"(line {candidate.line}, score {candidate.score})"
    )
    if args.github_output:
        with args.github_output.open("a", encoding="utf-8") as output:
            output.write("found=true\n")
            output.write(f"target={candidate.path}\n")
            output.write(f"anchor={candidate.anchor}\n")
            output.write(f"line={candidate.line}\n")


if __name__ == "__main__":
    main()

# PR smoke marker: final production behavior unchanged.
