#!/usr/bin/env python3
"""Validate every visible Lean counterpart link in the non-MF manuscript.

The non-MF paper uses the same

    \\leanverified{Criterion/FiniteDimensionalKill}{GroupApproximation.map_marked_commutator_eq_one}

surface as the property-(TT)/T paper, resolved against the same lexical Lean
declaration index used by ``check_lean_refs.py``.

One deliberate difference from ``check_property_tt_refs.py`` remains: not
every numbered result in the non-MF manuscript has a formal counterpart.  The
formal development includes the finite-dimensional core, the sequential
Kazhdan-compression kill, an independently constructed finitely presented
non-MF witness, the literal eight-generator presentation and its exact
nontrivial mark, the finite-normal obstruction, and the cofinite-corona MF
radical.  No unconditional MF endpoint is claimed for the literal group: its
two endpoints explicitly require either property `(T)` of the displayed base
or an exact rational SOS certificate.

This checker enforces both lexical resolution and a semantic contract for the
formal-status paragraph: its finitely presented non-MF sentence must link to
the standard ``IsOperatorMF`` endpoint pinned by ``scripts/Audit.lean``, not
to the project-local ``IsWeakMF`` auxiliary endpoint.  Transitive axiom
checking remains the responsibility of ``scripts/Audit.lean``.
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
DECLS_FILE = REPO / "docs" / "NON_MF_CLAIM_DECLS.txt"
REFERENCE_RE = re.compile(r"\\leanverified\{([^{}]+)\}\{([^{}]+)\}")
STATUS_RE = re.compile(
    r"\\begin\{remark\}\[status of the formal companion\]"
    r"\\label\{rem:leanstatus\}(.*?)\\end\{remark\}",
    re.DOTALL,
)
STATUS_ENDPOINT = (
    "Sofic/ChosenNonMFTheorem",
    "GroupApproximation.ChosenNonMFTheorem."
    "chosenFinitelyPresented_not_isOperatorMF",
)


def validate(repo: Path, tex: Path) -> list[str]:
    source = tex.read_text(encoding="utf-8")
    references = REFERENCE_RE.findall(source)
    if not references:
        return [f"no visible Lean counterpart links found in {tex.name}"]

    index = build_index(repo)
    problems: list[str] = []

    status_matches = STATUS_RE.findall(source)
    if len(status_matches) != 1:
        problems.append(
            "expected exactly one formal-status remark labelled rem:leanstatus"
        )
    else:
        status_references = REFERENCE_RE.findall(status_matches[0])
        if status_references.count(STATUS_ENDPOINT) != 1:
            problems.append(
                "formal-status finitely presented non-MF claim must link exactly "
                "once to the pinned chosen IsOperatorMF endpoint"
            )
        weak_endpoints = [
            declaration for _module, declaration in status_references
            if declaration.endswith("not_isWeakMF")
        ]
        if weak_endpoints:
            problems.append(
                "formal-status remark links an IsWeakMF auxiliary endpoint: "
                + ", ".join(weak_endpoints)
            )

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


def resolved_declarations(repo: Path, tex: Path) -> list[str]:
    """Fully qualified declarations named by valid visible counterpart links."""
    source = tex.read_text(encoding="utf-8")
    index = build_index(repo)
    out: set[str] = set()
    for module, declaration in REFERENCE_RE.findall(source):
        full = (declaration if declaration.startswith("GroupApproximation.")
                else f"GroupApproximation.{declaration}")
        expected = repo / "GroupApproximation" / f"{module}.lean"
        if index.get(full) == expected:
            out.add(full)
    return sorted(out)


def render_declarations(repo: Path, tex: Path) -> str:
    return "\n".join(resolved_declarations(repo, tex)) + "\n"


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
        endpoint = repo / "GroupApproximation" / "Sofic" / "ChosenNonMFTheorem.lean"
        endpoint.parent.mkdir(parents=True)
        endpoint.write_text(
            "namespace GroupApproximation.ChosenNonMFTheorem\n"
            "theorem chosenFinitelyPresented_not_isOperatorMF : True := by trivial\n"
            "theorem chosenFinitelyPresented_not_isWeakMF : True := by trivial\n"
            "end GroupApproximation.ChosenNonMFTheorem\n",
            encoding="utf-8",
        )
        elsewhere = repo / "GroupApproximation" / "Sofic"
        elsewhere.mkdir(parents=True, exist_ok=True)
        (elsewhere / "Stray.lean").write_text(
            "namespace GroupApproximation\n"
            "theorem strayed : True := by trivial\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        tex = repo / "paper.tex"

        correct_status = (
            r"\begin{remark}[status of the formal companion]"
            r"\label{rem:leanstatus}"
            r"\leanverified{Sofic/ChosenNonMFTheorem}"
            r"{GroupApproximation.ChosenNonMFTheorem."
            r"chosenFinitelyPresented_not_isOperatorMF}"
            r"\end{remark}"
        )
        tex.write_text(
            correct_status
            + r"\leanverified{Criterion/FiniteDimensionalKill}"
            + r"{GroupApproximation.map_marked_commutator_eq_one}",
            encoding="utf-8",
        )
        if validate(repo, tex):
            print("self-test: valid reference was rejected", file=sys.stderr)
            return 1

        self_decls = resolved_declarations(repo, tex)
        if self_decls != [
            "GroupApproximation.ChosenNonMFTheorem."
            "chosenFinitelyPresented_not_isOperatorMF",
            "GroupApproximation.map_marked_commutator_eq_one",
        ]:
            print("self-test: valid reference was not added to declaration roster",
                  file=sys.stderr)
            return 1

        tex.write_text(
            correct_status
            + r"\leanverified{Criterion/FiniteDimensionalKill}"
            + r"{GroupApproximation.map_marked_commutator_eq_two}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("missing declaration" in problem for problem in problems):
            print("self-test: missing declaration was not detected", file=sys.stderr)
            return 1

        tex.write_text(
            correct_status
            + r"\leanverified{Criterion/FiniteDimensionalKill}"
            + r"{GroupApproximation.strayed}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("is in" in problem for problem in problems):
            print("self-test: wrong-module reference was not detected",
                  file=sys.stderr)
            return 1

        weak_status = correct_status.replace(
            "chosenFinitelyPresented_not_isOperatorMF",
            "chosenFinitelyPresented_not_isWeakMF",
        )
        tex.write_text(weak_status, encoding="utf-8")
        problems = validate(repo, tex)
        if not any("pinned chosen IsOperatorMF endpoint" in problem
                   for problem in problems):
            print("self-test: WeakMF status drift was not detected",
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
    parser.add_argument("--write", action="store_true")
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

    rendered = render_declarations(REPO, tex)
    if args.write:
        DECLS_FILE.parent.mkdir(parents=True, exist_ok=True)
        DECLS_FILE.write_text(rendered, encoding="utf-8")
        print(f"wrote {DECLS_FILE.relative_to(REPO)}")
    elif not DECLS_FILE.is_file() or DECLS_FILE.read_text(encoding="utf-8") != rendered:
        print(f"check-non-mf-refs: stale {DECLS_FILE.relative_to(REPO)}; "
              "run scripts/check_non_mf_refs.py --write", file=sys.stderr)
        return 1

    count = len(REFERENCE_RE.findall(tex.read_text(encoding="utf-8")))
    print(f"check-non-mf-refs: {count} references all resolve")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
