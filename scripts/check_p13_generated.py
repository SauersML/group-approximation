#!/usr/bin/env python3
"""Regenerate and compare every machine-emitted P13 certificate source.

The Lean kernel is the authority for the proof.  This gate has a different,
strictly reproducibility-oriented job: it makes the four checked-in generators
operational and prevents the emitted finite data from drifting away from their
pinned JSON/NPZ inputs.  All output is written to a temporary directory.
"""

from __future__ import annotations

import argparse
import difflib
import re
import subprocess
import sys
import tempfile
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
EXPERIMENTS = REPO / "experiments"
LEAN = REPO / "GroupApproximation" / "Sofic"
REPLAY = EXPERIMENTS / "sl3-p13-reductions-complete.json"
CERTIFICATE = EXPERIMENTS / "sl3-sos-radius0-certificate.npz"
REPLAY_HELPER = EXPERIMENTS / "sl3_p13_relator_replay.py"


def run(*arguments: object) -> None:
    command = [sys.executable, *(str(argument) for argument in arguments)]
    subprocess.run(command, cwd=REPO, check=True)


def mismatch(expected: Path, generated: Path) -> None:
    expected_text = expected.read_text(encoding="utf-8")
    generated_text = generated.read_text(encoding="utf-8")
    if expected_text == generated_text:
        return
    excerpt = "".join(difflib.unified_diff(
        expected_text.splitlines(keepends=True),
        generated_text.splitlines(keepends=True),
        fromfile=str(expected.relative_to(REPO)),
        tofile=str(generated),
        n=3,
    ))
    raise RuntimeError(
        "generated P13 source drifted from the checked-in module:\n" +
        "".join(excerpt.splitlines(keepends=True)[:80]))


LEAN_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)


def lean_tokens(text: str) -> str:
    """Ignore layout and doc comments, but no executable Lean token."""
    without_comments = LEAN_COMMENT.sub("", text)
    return re.sub(r"\s+", "", without_comments)


def check_factor_fragment(generated: Path) -> None:
    generated_tokens = lean_tokens(generated.read_text(encoding="utf-8"))
    data_text = (LEAN / "LiteralP13HodgeData.lean").read_text(
        encoding="utf-8")
    start_marker = "def qNumeratorRow0 :"
    end_marker = "def qCoefficient (row : Fin 102)"
    if data_text.count(start_marker) != 1 or data_text.count(end_marker) != 1:
        raise RuntimeError(
            "canonical P13 Data module must contain exactly one Q-factor "
            "start marker and exactly one coefficient-definition marker")
    start = data_text.index(start_marker)
    end = data_text.index(end_marker)
    if start >= end:
        raise RuntimeError("canonical P13 Q-factor markers are out of order")
    canonical_tokens = lean_tokens(data_text[start:end])
    if generated_tokens != canonical_tokens:
        raise RuntimeError(
            "generated exact Q-factor fragment differs from the uniquely "
            "delimited operative factor in LiteralP13HodgeData.lean")


def generated_residual_names() -> list[str]:
    names: list[str] = []
    for left in range(6):
        for right in range(6):
            prefix = f"LiteralP13HodgeResidual{left}{right}"
            if left <= right:
                names.extend(f"{prefix}Part{part}.lean" for part in range(4))
            names.append(f"{prefix}.lean")
    names.append("LiteralP13HodgeResidual.lean")
    return names


def check(temporary_root: Path) -> None:
    temporary_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="p13-generated-", dir=temporary_root
    ) as directory:
        output = Path(directory)

        replay_output = output / "LiteralP13HodgeReplay.lean"
        run(EXPERIMENTS / "sl3_p13_replay_lean_generator.py",
            "--replay", REPLAY,
            "--replay-script", REPLAY_HELPER,
            "--certificate", CERTIFICATE,
            "--output", replay_output)
        mismatch(LEAN / replay_output.name, replay_output)

        pair_output = output / "LiteralP13HodgePairTable.lean"
        run(EXPERIMENTS / "sl3_p13_pair_table_generator.py",
            "--replay", REPLAY,
            "--output", pair_output)
        mismatch(LEAN / pair_output.name, pair_output)

        factor_output = output / "q-factor.lean"
        run(EXPERIMENTS / "sl3_p13_hodge_lean_generator.py",
            "--certificate", CERTIFICATE,
            "--output", factor_output)
        check_factor_fragment(factor_output)

        run(EXPERIMENTS / "sl3_p13_certificate_lean_generator.py",
            "--certificate", CERTIFICATE,
            "--replay", REPLAY,
            "--helper", REPLAY_HELPER,
            "--output-directory", output)
        for name in generated_residual_names():
            mismatch(LEAN / name, output / name)

    print("P13 generated-source replay: exact")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--temporary-root",
        type=Path,
        required=True,
        help="storage-backed parent for the generated-source replay",
    )
    arguments = parser.parse_args()
    check(arguments.temporary_root.resolve())


if __name__ == "__main__":
    main()
