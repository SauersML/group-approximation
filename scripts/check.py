#!/usr/bin/env python3
"""Check the source-level integrity of the Lean project."""

from __future__ import annotations

import argparse
import os
import re
import tempfile
from collections.abc import Iterable
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
LIBRARY = "GroupApproximation"
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.']+)", re.MULTILINE)

RULES = (
    ("sorry / sorryAx", re.compile(
        r"(?<![A-Za-z0-9_])(?:sorry|sorryAx)(?![A-Za-z0-9_])")),
    ("admit", re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])")),
    ("hand-declared axiom", re.compile(r"^[ \t]*axiom[ \t]", re.MULTILINE)),
    ("native_decide", re.compile(
        r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])")),
    ("unsafe escape hatch", re.compile(
        r"(?<![A-Za-z0-9_])(?:unsafe|implemented_by|opaque)(?![A-Za-z0-9_])")),
    ("warningAsError disabled", re.compile(
        r"warningAsError[ \t]*(?::=)?[ \t]*false")),
    ("maxHeartbeats override", re.compile(
        r"set_option[ \t]+(?:[A-Za-z0-9_]+\.)*maxHeartbeats\b")),
    ("maxRecDepth override", re.compile(
        r"set_option[ \t]+(?:[A-Za-z0-9_]+\.)*maxRecDepth\b")),
)

ALLOWLIST = {
    ("sorry / sorryAx", "Palomar/Challenge.lean", "sorry"),
    ("hand-declared axiom", "scripts/Audit/Plants.lean",
     "axiom plantedAxiom : True"),
}


def mask_noncode(source: str) -> str:
    """Mask nested comments and strings while preserving offsets and lines."""
    out = list(source)
    depth = 0
    i = 0
    while i < len(source):
        if depth == 0 and source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if source.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth and source.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth:
            if source[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if source[i] == '"':
            out[i] = " "
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    out[i] = " "
                    if i + 1 < len(source):
                        out[i + 1] = " "
                    i += 2
                elif source[i] == '"':
                    out[i] = " "
                    i += 1
                    break
                else:
                    if source[i] != "\n":
                        out[i] = " "
                    i += 1
            continue
        i += 1
    return "".join(out)


def lean_sources(root: Path) -> list[Path]:
    paths: list[Path] = []
    for directory, subdirectories, filenames in os.walk(root):
        subdirectories[:] = [
            name for name in subdirectories if name not in {".git", ".lake", ".venv"}
        ]
        paths.extend(
            Path(directory) / name for name in filenames if name.endswith(".lean")
        )
    return sorted(paths)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def scan_file(root: Path, path: Path) -> list[tuple[str, str]]:
    source = path.read_text(encoding="utf-8")
    masked = mask_noncode(source)
    relative = path.relative_to(root).as_posix()
    findings: list[tuple[str, str]] = []
    for label, pattern in RULES:
        for match in pattern.finditer(masked):
            line = line_number(source, match.start())
            text = source.splitlines()[line - 1].strip()
            if (label, relative, text) in ALLOWLIST:
                continue
            findings.append((label, f"{relative}:{line}: {text}"))

    command_seen = False
    for number, line in enumerate(masked.splitlines(), 1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped == "prelude" and not command_seen:
            continue
        if stripped.startswith("import "):
            if command_seen:
                findings.append((
                    "late import", f"{relative}:{number}: import follows a command"
                ))
        else:
            command_seen = True
    return findings


def modules(root: Path) -> dict[str, Path]:
    result = {LIBRARY: root / f"{LIBRARY}.lean"}
    for path in sorted((root / LIBRARY).rglob("*.lean")):
        result[".".join(path.relative_to(root).with_suffix("").parts)] = path
    return result


def orphan_modules(root: Path) -> list[str]:
    available = modules(root)
    if not available[LIBRARY].is_file():
        return [f"missing root module {LIBRARY}.lean"]
    seen: set[str] = set()
    pending = [LIBRARY]
    while pending:
        name = pending.pop()
        if name in seen or name not in available:
            continue
        seen.add(name)
        source = mask_noncode(available[name].read_text(encoding="utf-8"))
        pending.extend(
            imported for imported in IMPORT_RE.findall(source)
            if imported == LIBRARY or imported.startswith(f"{LIBRARY}.")
        )
    return sorted(set(available) - seen)


def check(root: Path) -> tuple[list[tuple[str, str]], int]:
    paths = lean_sources(root)
    findings = [finding for path in paths for finding in scan_file(root, path)]
    findings.extend(
        ("orphan module", name) for name in orphan_modules(root)
    )

    challenge = root / "Palomar" / "Challenge.lean"
    if challenge.is_file():
        count = len(re.findall(
            r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])",
            mask_noncode(challenge.read_text(encoding="utf-8")),
        ))
        if count != 1:
            findings.append((
                "challenge contract",
                f"Palomar/Challenge.lean contains {count} `sorry` tokens; expected 1",
            ))
    else:
        findings.append(("challenge contract", "Palomar/Challenge.lean is missing"))
    return findings, len(paths)


def self_test() -> None:
    snippets = {
        "sorry / sorryAx": "theorem bad : True := by sorry\n",
        "admit": "theorem bad : True := by admit\n",
        "hand-declared axiom": "axiom bad : True\n",
        "native_decide": "example : True := by native_decide\n",
        "unsafe escape hatch": "unsafe def bad : Nat := 0\n",
        "warningAsError disabled": "set_option warningAsError false\n",
        "maxHeartbeats override": "set_option maxHeartbeats 1 in\n#check Nat\n",
        "maxRecDepth override": "set_option maxRecDepth 1 in\n#check Nat\n",
        "late import": "def x := 1\nimport Mathlib\n",
    }
    with tempfile.TemporaryDirectory(prefix="source-check-") as directory:
        root = Path(directory)
        path = root / "Probe.lean"
        for expected, source in snippets.items():
            path.write_text(source, encoding="utf-8")
            labels = {label for label, _ in scan_file(root, path)}
            if expected not in labels:
                raise AssertionError(f"{expected} detector did not fire")

        path.write_text(
            '/- sorry axiom native_decide -/\ndef safe := "opaque admit"\n',
            encoding="utf-8",
        )
        if scan_file(root, path):
            raise AssertionError("comments or strings produced a false positive")

        library = root / LIBRARY
        library.mkdir()
        (root / f"{LIBRARY}.lean").write_text(
            f"import {LIBRARY}.Used\n", encoding="utf-8"
        )
        (library / "Used.lean").write_text("def used := True\n", encoding="utf-8")
        (library / "Orphan.lean").write_text("def orphan := True\n", encoding="utf-8")
        if orphan_modules(root) != [f"{LIBRARY}.Orphan"]:
            raise AssertionError("orphan-module detector did not fire exactly")
    print(f"source scan self-test: {len(snippets) + 2} checks passed")


def report(findings: Iterable[tuple[str, str]], source_count: int) -> int:
    rows = list(findings)
    for label, detail in rows:
        print(f"::error::[{label}] {detail}")
    labels = [label for label, _ in RULES] + [
        "late import", "orphan module", "challenge contract"
    ]
    for label in labels:
        print(f"{label}: {sum(found == label for found, _ in rows)}")
    print(f"source scan: {source_count} Lean sources, {len(rows)} findings")
    return 1 if rows else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    if arguments.self_test:
        self_test()
        return 0
    findings, count = check(REPO)
    return report(findings, count)


if __name__ == "__main__":
    raise SystemExit(main())
