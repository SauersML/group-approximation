#!/usr/bin/env python3
"""Validate every visible Lean counterpart link in the non-MF manuscript.

The non-MF paper uses the same

    \\leanverified{Criterion/FiniteDimensionalKill}{GroupApproximation.map_marked_commutator_eq_one}

surface as the property-(TT)/T paper, resolved against the same lexical Lean
declaration index used by ``check_lean_refs.py``.

One deliberate difference from ``check_property_tt_refs.py`` remains: not
every numbered result in the non-MF manuscript has a formal counterpart.  The
formal development now includes the finite-dimensional core, the sequential
Kazhdan-compression kill, and an independently constructed finitely presented
non-MF witness.  The paper's literal eight-generator presentation and its
finite-normal strengthening are paper proofs, not Lean claims.  Accordingly
this checker enforces that every counterpart link that *is* claimed resolves
to a real declaration in the named module; statement pinning and transitive
axiom checking of the formal headline endpoints are performed separately by
``scripts/Audit.lean``.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import build_index


REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
REFERENCE_RE = re.compile(r"\\leanverified\{([^{}]+)\}\{([^{}]+)\}")


def validate(repo: Path, tex: Path) -> list[str]:
    source = tex.read_text(encoding="utf-8")
    references = REFERENCE_RE.findall(source)
    if not references:
        return [f"no visible Lean counterpart links found in {tex.name}"]

    index = build_index(repo)
    problems: list[str] = []
    for module, declaration in references:
        expected = repo / "GroupApproximation" / f"{module}.lean"
        full_name = (declaration if declaration.startswith("GroupApproximation.")
                     else f"GroupApproximation.{declaration}")
        actual = index.get(full_name)
        if not expected.is_file():
            problems.append(f"missing module file GroupApproximation/{module}.lean")
        if actual is None:
            problems.append(f"missing declaration {full_name}")
        elif actual.resolve() != expected.resolve():
            problems.append(
                f"{full_name} is in {actual.relative_to(repo)}, not "
                f"GroupApproximation/{module}.lean"
            )
    return problems


def self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        repo = Path(directory)
        module = repo / "GroupApproximation" / "Criterion"
        module.mkdir(parents=True)
        (module / "FiniteDimensionalKill.lean").write_text(
            "namespace GroupApproximation\n"
            "theorem map_marked_commutator_eq_one : True := by trivial\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        elsewhere = repo / "GroupApproximation" / "Sofic"
        elsewhere.mkdir(parents=True)
        (elsewhere / "Stray.lean").write_text(
            "namespace GroupApproximation\n"
            "theorem strayed : True := by trivial\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        tex = repo / "paper.tex"

        tex.write_text(
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.map_marked_commutator_eq_one}",
            encoding="utf-8",
        )
        if validate(repo, tex):
            print("self-test: valid reference was rejected", file=sys.stderr)
            return 1

        tex.write_text(
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.map_marked_commutator_eq_two}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("missing declaration" in problem for problem in problems):
            print("self-test: missing declaration was not detected", file=sys.stderr)
            return 1

        tex.write_text(
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.strayed}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("is in" in problem for problem in problems):
            print("self-test: wrong-module reference was not detected",
                  file=sys.stderr)
            return 1

        tex.write_text("no links here", encoding="utf-8")
        problems = validate(repo, tex)
        if not any("no visible Lean counterpart links" in problem
                   for problem in problems):
            print("self-test: linkless manuscript was not detected",
                  file=sys.stderr)
            return 1
    print("check-non-mf-refs: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()

    tex = args.tex if args.tex.is_absolute() else REPO / args.tex
    problems = validate(REPO, tex)
    if problems:
        print(f"check-non-mf-refs: {len(problems)} problem(s):", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    count = len(REFERENCE_RE.findall(tex.read_text(encoding="utf-8")))
    print(f"check-non-mf-refs: {count} references all resolve")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
