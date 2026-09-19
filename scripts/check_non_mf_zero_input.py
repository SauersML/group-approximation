#!/usr/bin/env python3
"""Require every Lean declaration cited by the non-MF paper to be zero-input.

For the publication interface, quantifiers belong inside the proposition:

    theorem endpoint : ∀ (G : Type) [Group G], P G := ...

and not in the declaration header:

    theorem endpoint (G : Type) [Group G] : P G := ...

The two forms elaborate to the same kernel type, but the first makes the
closed status of a manuscript endpoint visible and mechanically auditable.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import MODIFIERS, _strip_block_comments


LEAN_REF = re.compile(r"\\leanverified\{([^}]+)\}\{([^}]+)\}")

# The keywords a cited manuscript endpoint can be introduced by.  `abbrev` and
# `instance` are here for the same reason `lean_decls.py` indexes them: a badge
# may cite one, and a keyword this scanner does not know about is reported as a
# missing declaration rather than as a checked one.
KEYWORDS = ("theorem", "lemma", "def", "abbrev", "instance")


def declaration_is_zero_input(source: str, short_name: str) -> bool:
    # Comments are stripped before the search.  A module docstring may quote a
    # declaration it does not contain -- a fenced sketch of a step that is not
    # yet proved is the common case -- and a scanner reading raw source cannot
    # tell that quotation from the real thing.  It would then report a badge as
    # checked whose declaration does not exist at all, which is a worse failure
    # than the one this gate was written to catch.  `check_non_mf_unconditional`
    # already strips for the same reason.
    source = _strip_block_comments(source)
    declaration = re.compile(
        rf"(?m)^\s*{MODIFIERS}(?:{'|'.join(KEYWORDS)})\s+(?:[A-Za-z0-9_'.]+\.)?"
        rf"{re.escape(short_name)}\b"
    )
    match = declaration.search(source)
    if match is None:
        raise ValueError("declaration not found")
    remainder = source[match.end() :].lstrip()
    return remainder.startswith(":")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", default="non_mf_groups_exist.tex")
    parser.add_argument("--root", default=".")
    args = parser.parse_args()

    root = Path(args.root)
    tex = (root / args.tex).read_text(encoding="utf-8")
    problems: list[str] = []
    checked = 0

    for line_number, line in enumerate(tex.splitlines(), start=1):
        for module, declaration in LEAN_REF.findall(line):
            checked += 1
            source_path = root / "GroupApproximation" / f"{module}.lean"
            if not source_path.is_file():
                problems.append(f"line {line_number}: missing {source_path}")
                continue
            short_name = declaration.rsplit(".", 1)[-1]
            try:
                closed = declaration_is_zero_input(
                    source_path.read_text(encoding="utf-8"), short_name
                )
            except ValueError:
                problems.append(
                    f"line {line_number}: declaration {declaration} not found"
                )
                continue
            if not closed:
                problems.append(
                    f"line {line_number}: {declaration} has declaration inputs; "
                    "move every binder after the colon"
                )

    if problems:
        print(f"check-non-mf-zero-input: {len(problems)} problem(s):")
        for problem in problems:
            print(f"  {problem}")
        return 1

    print(f"check-non-mf-zero-input: {checked} cited declarations are closed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
