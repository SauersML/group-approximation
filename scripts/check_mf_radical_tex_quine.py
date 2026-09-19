#!/usr/bin/env python3
"""Independently verify the exact TeX quine and Lean byte ledger."""

from __future__ import annotations

import ast
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

from build_mf_radical_tex_quine import quine_bytes


ROOT = Path(__file__).resolve().parent.parent
TEX = ROOT / "mf_radical_tex_quine.tex"
LEAN = ROOT / "GroupApproximation/Computability/MFRadicalQuineSource.lean"
BEGIN = "% QUINE-PROGRAM-BEGIN"
END = "% QUINE-PROGRAM-END"
LIST_BEGIN = "-- MANUSCRIPT-BYTES-BEGIN"
LIST_END = "-- MANUSCRIPT-BYTES-END"


def between_exact_lines(text: str, begin: str, end: str) -> list[str]:
    lines = text.splitlines()
    begin_positions = [i for i, line in enumerate(lines) if line == begin]
    end_positions = [i for i, line in enumerate(lines) if line == end]
    if len(begin_positions) != 1 or len(end_positions) != 1:
        raise AssertionError(f"expected one exact {begin!r}/{end!r} pair")
    lo, hi = begin_positions[0], end_positions[0]
    if lo >= hi:
        raise AssertionError("marker order is invalid")
    return lines[lo + 1 : hi]


def extract_program(tex: str) -> str:
    block = between_exact_lines(tex, BEGIN, END)
    if block[0] != r"\begin{lstlisting}[language=Python]":
        raise AssertionError("unexpected listing start")
    if block[-1] != r"\end{lstlisting}":
        raise AssertionError("unexpected listing end")
    return "\n".join(block[1:-1]) + "\n"


def extract_lean_bytes(lean: str) -> bytes:
    block = between_exact_lines(lean, LIST_BEGIN, LIST_END)
    payload = "\n".join(block)
    prefix = "def manuscriptBytes : List ℕ := "
    if not payload.startswith(prefix):
        raise AssertionError("unexpected Lean byte declaration")
    values = ast.literal_eval(payload[len(prefix) :])
    if not isinstance(values, list):
        raise AssertionError("Lean byte ledger is not a list")
    if any(type(value) is not int or not 0 <= value < 256 for value in values):
        raise AssertionError("Lean byte ledger contains a non-byte")
    return bytes(values)


def main() -> None:
    actual = TEX.read_bytes()
    expected = quine_bytes()
    if actual != expected:
        raise AssertionError("TeX file differs from the canonical fixed point")

    text = actual.decode("ascii")
    program = extract_program(text)
    with tempfile.TemporaryDirectory(prefix="mf-radical-quine-") as directory:
        completed = subprocess.run(
            [sys.executable, "-I", "-c", program],
            cwd=directory,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    if completed.returncode != 0:
        raise AssertionError(
            "embedded quine failed:\n" + completed.stderr.decode("utf-8", "replace")
        )
    if completed.stderr:
        raise AssertionError("embedded quine wrote to stderr")
    if completed.stdout != actual:
        raise AssertionError("embedded quine output differs byte-for-byte")

    ledger = extract_lean_bytes(LEAN.read_text(encoding="utf-8"))
    if ledger != actual:
        raise AssertionError("Lean byte ledger differs from the TeX source")

    digest = hashlib.sha256(actual).hexdigest()
    print(f"exact TeX quine: {len(actual)} bytes, sha256={digest}")
    print("embedded program output, canonical generator, and Lean ledger all match")


if __name__ == "__main__":
    main()
