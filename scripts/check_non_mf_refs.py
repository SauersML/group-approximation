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
algebraic, finite-dimensional, and universal-Horn boundary is formalized,
but no analytic operator-MF endpoint for it is part of the Lean API.

This checker enforces both lexical resolution and an exact semantic contract
for the margin links.  The reviewed whitelist below is deliberately closed:
adding a true but weaker component theorem, a conditional bridge, or a badge
whose surrounding prose claims more than its type is a source-review event,
not something lexical declaration lookup may silently approve.  Transitive
axiom checking remains the responsibility of ``scripts/Audit.lean``.
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
UNCONDITIONAL_ENDPOINT = (
    "Sofic/ChosenNonMFTheorem",
    "GroupApproximation.ChosenNonMFTheorem."
    "exists_finitelyPresented_not_isOperatorMF",
)
APPROVED_REFERENCES = frozenset({
    UNCONDITIONAL_ENDPOINT,
    ("Criterion/CompressionCentralizerDefect",
     "GroupApproximation.compressionCentralizerDefect_le_ker"),
    ("Monsters/AffineSL3Doubling",
     "GroupApproximation.AffineSL3Doubling.doubling_package"),
    ("Sofic/LiteralNonMFLinearWitness",
     "GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one"),
    ("Sofic/LiteralFiniteDimensionalObstruction",
     "GroupApproximation.LiteralFiniteDimensionalObstruction."
     "literal_finiteDimensional_rep_not_injective"),
    ("Sofic/CompressionDefectSquare",
     "GroupApproximation."
     "commutator_conjugate_eq_commutator_sq_of_sq_eq_one"),
    ("Sofic/ChosenUniversalHorn",
     "GroupApproximation.ChosenUniversalHorn."
     "isOperatorMF_satisfies_chosenQuasiIdentity"),
    ("Sofic/ChosenUniversalHorn",
     "GroupApproximation.ChosenUniversalHorn."
     "markedGroup_not_satisfies_chosenQuasiIdentity"),
    ("Analysis/FaithfulTracialMatrix",
     "GroupApproximation.FaithfulTracialState."
     "matrix_mul_star_eq_one_of_star_mul_eq_one"),
    ("Sofic/MarkedMFClosed",
     "GroupApproximation.MarkedGroupSpace.isClosed_operatorMFLocus"),
    ("Sofic/ChosenMarkedCylinder",
     "GroupApproximation.ChosenMarkedCylinder.chosenCylinder_isClopen"),
    ("Sofic/ChosenMarkedCylinder",
     "GroupApproximation.ChosenMarkedCylinder.chosenCylinder_subset_nonMF"),
})
RETIRED_EXPLICIT_MODULES = frozenset({
    "Sofic/ExplicitMarkedPresentation",
    "Sofic/ExplicitNonMFEndpoint",
    "Sofic/ExplicitNonMFTheorem",
})


def validate(repo: Path, tex: Path) -> list[str]:
    source = tex.read_text(encoding="utf-8")
    references = REFERENCE_RE.findall(source)
    if not references:
        return [f"no visible Lean counterpart links found in {tex.name}"]

    index = build_index(repo)
    problems: list[str] = []

    unapproved = sorted(set(references) - APPROVED_REFERENCES)
    if unapproved:
        problems.append(
            "margin links outside the reviewed exact whitelist: "
            + ", ".join(f"{module}:{declaration}"
                        for module, declaration in unapproved)
        )

    missing = sorted(APPROVED_REFERENCES - set(references))
    if missing:
        problems.append(
            "reviewed exact margin links missing from the manuscript: "
            + ", ".join(f"{module}:{declaration}"
                        for module, declaration in missing)
        )

    if references.count(UNCONDITIONAL_ENDPOINT) != 1:
        problems.append(
            "margin links must name exactly once the pinned unconditional "
            "IsOperatorMF existence endpoint"
        )

    weak_endpoints = [
        declaration for _module, declaration in references
        if "WeakMF" in declaration
    ]
    if weak_endpoints:
        problems.append(
            "margin links an IsWeakMF auxiliary endpoint: "
            + ", ".join(weak_endpoints)
        )

    retired = [
        f"{module}:{declaration}" for module, declaration in references
        if module in RETIRED_EXPLICIT_MODULES
    ]
    if retired:
        problems.append(
            "margin links a retired explicit endpoint: " + ", ".join(retired)
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
            "theorem exists_finitelyPresented_not_isOperatorMF : True := by trivial\n"
            "theorem chosenFinitelyPresented_not_isWeakMF : True := by trivial\n"
            "end GroupApproximation.ChosenNonMFTheorem\n",
            encoding="utf-8",
        )
        retired = repo / "GroupApproximation" / "Sofic" / "ExplicitNonMFTheorem.lean"
        retired.write_text(
            "namespace GroupApproximation.ExplicitNonMFTheorem\n"
            "theorem retired : True := by trivial\n"
            "end GroupApproximation.ExplicitNonMFTheorem\n",
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

        correct_endpoint = (
            r"\leanverified{Sofic/ChosenNonMFTheorem}"
            r"{GroupApproximation.ChosenNonMFTheorem."
            r"exists_finitelyPresented_not_isOperatorMF}"
        )
        tex.write_text(
            correct_endpoint
            + r"\leanverified{Criterion/FiniteDimensionalKill}"
            + r"{GroupApproximation.map_marked_commutator_eq_one}",
            encoding="utf-8",
        )
        self_decls = resolved_declarations(repo, tex)
        if self_decls != [
            "GroupApproximation.ChosenNonMFTheorem."
            "exists_finitelyPresented_not_isOperatorMF",
            "GroupApproximation.map_marked_commutator_eq_one",
        ]:
            print("self-test: valid reference was not added to declaration roster",
                  file=sys.stderr)
            return 1

        tex.write_text(
            correct_endpoint
            + r"\leanverified{Criterion/FiniteDimensionalKill}"
            + r"{GroupApproximation.map_marked_commutator_eq_two}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("missing declaration" in problem for problem in problems):
            print("self-test: missing declaration was not detected", file=sys.stderr)
            return 1

        tex.write_text(
            correct_endpoint
            + r"\leanverified{Criterion/FiniteDimensionalKill}"
            + r"{GroupApproximation.strayed}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("is in" in problem for problem in problems):
            print("self-test: wrong-module reference was not detected",
                  file=sys.stderr)
            return 1

        tex.write_text(
            correct_endpoint
            + correct_endpoint,
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("exactly once" in problem
                   for problem in problems):
            print("self-test: duplicate unconditional endpoint was not detected",
                  file=sys.stderr)
            return 1

        tex.write_text(
            correct_endpoint
            + r"\leanverified{Sofic/ChosenNonMFTheorem}"
            + r"{GroupApproximation.ChosenNonMFTheorem."
            + r"chosenFinitelyPresented_not_isWeakMF}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("IsWeakMF auxiliary endpoint" in problem for problem in problems):
            print("self-test: WeakMF endpoint was not rejected", file=sys.stderr)
            return 1

        tex.write_text(
            correct_endpoint
            + r"\leanverified{Sofic/ExplicitNonMFTheorem}"
            + r"{GroupApproximation.ExplicitNonMFTheorem.retired}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("retired explicit endpoint" in problem for problem in problems):
            print("self-test: retired explicit endpoint was not rejected",
                  file=sys.stderr)
            return 1

        tex.write_text(
            correct_endpoint
            + r"\leanverified{Sofic/Stray}"
            + r"{GroupApproximation.strayed}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("outside the reviewed exact whitelist" in problem
                   for problem in problems):
            print("self-test: unapproved reference was not rejected",
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
