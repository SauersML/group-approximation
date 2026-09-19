#!/usr/bin/env python3
"""Validate Lean counterpart links in the non-MF manuscript.

Six certification statuses are accepted:

    \\leanverified{Module/Path}{GroupApproximation.theorem}
    \\leanequivalent{Module/Path}{GroupApproximation.theorem}
    \\leansupporting{Module/Path}{GroupApproximation.theorem}
    \\leanconditional{Module/Path}{GroupApproximation.theorem}
    \\leanpartial{Module/Path}{GroupApproximation.theorem}
    \\leandifferentwitness{Module/Path}{GroupApproximation.theorem}

``leanverified`` is reserved for an object-level proof of the printed claim.
The other statuses respectively record a proved equivalent formulation, a
supporting lemma, a theorem retaining an extra premise, a proper subclaim, or
the same existential conclusion with a different witness.  The checker never
promotes any of those five statuses to a verified endpoint.

The checker provides three independent safeguards:

* every badge invocation has exactly two nonempty, syntactically valid
  arguments;
* every cited declaration exists in the named module;
* ``metadata/NON_MF_CLAIM_DECLS.txt`` can be checked as a generated roster of all
  cited declarations, giving proposition-signature tooling complete input
  rather than the former hand-selected seven names.

An exact literal endpoint can additionally be required with
``--require-verified MODULE DECLARATION``.  A conditional citation of that
declaration does not satisfy the requirement.  This is the truthful
replacement for the former hardcoded requirement that the manuscript cite an
unrelated chosen-witness theorem.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check import orphan_paths
from lean_decls import build_index


REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "non_mf_groups_exist.tex"
DEFAULT_DECLS = REPO / "metadata" / "NON_MF_CLAIM_DECLS.txt"

STATUSES = (
    "verified",
    "equivalent",
    "supporting",
    "conditional",
    "partial",
    "differentwitness",
)
BADGE_RE = re.compile(
    r"\\lean(?P<status>" + "|".join(STATUSES) + r")\b"
)
DEFINITION_RE = re.compile(
    r"\\(?:re)?newcommand\s*\{\s*\\lean(?:"
    + "|".join(STATUSES)
    + r")\s*\}"
)
MODULE_RE = re.compile(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*\Z")
DECLARATION_RE = re.compile(r"[^\s{}]+\Z")

RETIRED_HEADLINE_FRAGMENTS = (
    "Sofic/ExplicitNonMFTheorem",
    "GroupApproximation.ExplicitNonMFTheorem",
    "explicit_finitelyPresented",
)


@dataclass(frozen=True)
class Reference:
    status: str
    module: str
    declaration: str
    line: int

    @property
    def full_name(self) -> str:
        if self.declaration.startswith("GroupApproximation."):
            return self.declaration
        return f"GroupApproximation.{self.declaration}"


def _strip_comments(source: str) -> str:
    """Remove TeX comments while preserving newlines and line numbers."""
    out: list[str] = []
    for line in source.splitlines(keepends=True):
        cut = len(line)
        for i, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            j = i - 1
            while j >= 0 and line[j] == "\\":
                backslashes += 1
                j -= 1
            if backslashes % 2 == 0:
                cut = i
                break
        suffix = "\n" if line.endswith("\n") else ""
        out.append(line[:cut].rstrip("\n") + suffix)
    return "".join(out)


def _definition_badge_spans(source: str) -> list[tuple[int, int]]:
    """Return badge-token spans occurring inside macro definitions."""
    spans: list[tuple[int, int]] = []
    for definition in DEFINITION_RE.finditer(source):
        badge = BADGE_RE.search(source, definition.start(), definition.end())
        if badge is not None:
            spans.append(badge.span())
    return spans


def _parse_argument(source: str, cursor: int) -> tuple[str | None, int, str | None]:
    while cursor < len(source) and source[cursor].isspace():
        cursor += 1
    if cursor >= len(source) or source[cursor] != "{":
        return None, cursor, "expected a braced argument"
    end = source.find("}", cursor + 1)
    if end == -1:
        return None, len(source), "unterminated braced argument"
    value = source[cursor + 1:end]
    if "{" in value:
        return None, end + 1, "nested braces are not allowed in badge arguments"
    value = value.strip()
    if not value:
        return None, end + 1, "badge arguments must be nonempty"
    return value, end + 1, None


def parse_references(source: str) -> tuple[list[Reference], list[str]]:
    """Parse badge invocations and report malformed syntax with line numbers."""
    source = _strip_comments(source)
    definitions = set(_definition_badge_spans(source))
    references: list[Reference] = []
    problems: list[str] = []

    for badge in BADGE_RE.finditer(source):
        if badge.span() in definitions:
            continue
        line = source.count("\n", 0, badge.start()) + 1
        module, cursor, error = _parse_argument(source, badge.end())
        if error is not None:
            problems.append(f"line {line}: malformed \\lean{badge['status']}: {error}")
            continue
        declaration, cursor, error = _parse_argument(source, cursor)
        if error is not None:
            problems.append(f"line {line}: malformed \\lean{badge['status']}: {error}")
            continue
        assert module is not None and declaration is not None
        while cursor < len(source) and source[cursor].isspace():
            cursor += 1
        if cursor < len(source) and source[cursor] == "{":
            problems.append(
                f"line {line}: malformed \\lean{badge['status']}: expected exactly two arguments"
            )
            continue
        if MODULE_RE.fullmatch(module) is None:
            problems.append(
                f"line {line}: invalid module path `{module}`; use slash-separated Lean identifiers"
            )
            continue
        if DECLARATION_RE.fullmatch(declaration) is None:
            problems.append(f"line {line}: invalid declaration name `{declaration}`")
            continue
        references.append(Reference(badge["status"], module, declaration, line))

    return references, problems


def validate(repo: Path, tex: Path) -> tuple[list[Reference], list[str]]:
    references, problems = parse_references(tex.read_text(encoding="utf-8"))
    if not references and not problems:
        problems.append(f"no Lean counterpart links found in {tex.name}")
        return references, problems

    index = build_index(repo)
    # A badge over an uncompiled module is the worst thing this checker can
    # miss.  `lake build` reaches only the root's import closure, so a module
    # outside it is never elaborated, never reaches `#print axioms`, and is
    # never seen by the kernel audit -- yet its badge renders in the PDF
    # identically to one over a fully verified endpoint.  That is a claim of
    # verification for something unverified.  Fail closed: if the closure
    # cannot be computed, certify nothing rather than everything.
    try:
        orphans = orphan_paths(repo)
    except OSError as error:
        orphans = None
        problems.append(
            f"cannot compute the import closure, so no badge can be certified: {error}"
        )
    for reference in references:
        module = reference.module
        declaration = reference.declaration
        if orphans is not None and module in orphans:
            problems.append(
                f"line {reference.line}: badge cites GroupApproximation/{module}.lean, "
                "which is outside the import closure of GroupApproximation.lean; "
                "`lake build` never compiles it and no audit ever sees "
                f"{reference.full_name}, so the badge certifies nothing"
            )
        if "not_isWeakMF" in declaration:
            problems.append(
                f"line {reference.line}: auxiliary IsWeakMF theorem used as a manuscript "
                f"counterpart: {declaration}; use an IsOperatorMF endpoint"
            )
        if any(fragment in module or fragment in declaration
               for fragment in RETIRED_HEADLINE_FRAGMENTS):
            problems.append(
                f"line {reference.line}: retired Explicit* chosen-witness reference: "
                f"{module} / {declaration}"
            )
        expected = repo / "GroupApproximation" / f"{module}.lean"
        actual = index.get(reference.full_name)
        if not expected.is_file():
            problems.append(
                f"line {reference.line}: missing module file GroupApproximation/{module}.lean"
            )
        if actual is None:
            problems.append(
                f"line {reference.line}: missing declaration {reference.full_name}"
            )
        elif actual.resolve() != expected.resolve():
            problems.append(
                f"line {reference.line}: {reference.full_name} is in "
                f"{actual.relative_to(repo)}, not GroupApproximation/{module}.lean"
            )
    return references, problems


def render_declarations(references: list[Reference]) -> str:
    """Render the deterministic declaration roster consumed by CI."""
    return "".join(f"{name}\n" for name in sorted({ref.full_name for ref in references}))


def check_required_verified(
    references: list[Reference], required: list[tuple[str, str]]
) -> list[str]:
    problems: list[str] = []
    verified = {(ref.module, ref.full_name) for ref in references
                if ref.status == "verified"}
    nonverified = {
        (ref.module, ref.full_name): ref.status
        for ref in references if ref.status != "verified"
    }
    for module, declaration in required:
        full_name = (declaration if declaration.startswith("GroupApproximation.")
                     else f"GroupApproximation.{declaration}")
        key = (module, full_name)
        if key in verified:
            continue
        if key in nonverified:
            problems.append(
                f"required literal endpoint {full_name} in {module} is cited only as "
                f"\\lean{nonverified[key]}; an exact \\leanverified citation is required"
            )
        else:
            problems.append(
                f"missing required verified literal endpoint {full_name} in {module}"
            )
    return problems


def check_required_status(
    references: list[Reference], required: list[tuple[str, str, str]]
) -> list[str]:
    """Require an exact certification status for a cited declaration."""
    problems: list[str] = []
    cited = {
        (ref.status, ref.module, ref.full_name)
        for ref in references
    }
    statuses_by_claim = {
        (ref.module, ref.full_name): ref.status
        for ref in references
    }
    for status, module, declaration in required:
        full_name = (declaration if declaration.startswith("GroupApproximation.")
                     else f"GroupApproximation.{declaration}")
        if (status, module, full_name) in cited:
            continue
        actual = statuses_by_claim.get((module, full_name))
        if actual is None:
            problems.append(
                f"missing required \\lean{status} citation of {full_name} in {module}"
            )
        else:
            problems.append(
                f"required {full_name} in {module} to be cited as \\lean{status}, "
                f"but it is \\lean{actual}"
            )
    return problems


def self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        repo = Path(directory)
        criterion = repo / "GroupApproximation" / "Criterion"
        criterion.mkdir(parents=True)
        (criterion / "FiniteDimensionalKill.lean").write_text(
            "namespace GroupApproximation\n"
            "theorem map_marked_commutator_eq_one : True := by trivial\n"
            "theorem conditional_endpoint (h : True) : True := by trivial\n"
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
        # The root imports only the first module, so `Sofic/Stray` is a genuine
        # orphan in this corpus -- which is what calibrates the closure gate
        # below in both directions.
        (repo / "GroupApproximation.lean").write_text(
            "import GroupApproximation.Criterion.FiniteDimensionalKill\n",
            encoding="utf-8",
        )
        tex = repo / "paper.tex"
        valid = (
            r"\newcommand{\leanverified}[2]{}" "\n"
            r"\newcommand{\leanconditional}[2]{}" "\n"
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.map_marked_commutator_eq_one}" "\n"
            r"\leanconditional{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.conditional_endpoint}"
        )
        tex.write_text(valid, encoding="utf-8")
        references, problems = validate(repo, tex)
        if problems or len(references) != 2:
            print(f"self-test: valid references were rejected: {problems}", file=sys.stderr)
            return 1

        expected_roster = (
            "GroupApproximation.conditional_endpoint\n"
            "GroupApproximation.map_marked_commutator_eq_one\n"
        )
        if render_declarations(references) != expected_roster:
            print("self-test: declaration roster is not deterministic", file=sys.stderr)
            return 1

        requirement = [("Criterion/FiniteDimensionalKill",
                        "GroupApproximation.conditional_endpoint")]
        required_problems = check_required_verified(references, requirement)
        if not any("cited only as" in problem for problem in required_problems):
            print("self-test: conditional endpoint satisfied verified requirement",
                  file=sys.stderr)
            return 1
        verified_source = valid.replace(r"\leanconditional", r"\leanverified")
        verified_references, verified_problems = validate(
            repo, _write(tex, verified_source)
        )
        if verified_problems or check_required_verified(verified_references, requirement):
            print("self-test: verified endpoint did not satisfy requirement", file=sys.stderr)
            return 1

        status_requirement = [(
            "conditional", "Criterion/FiniteDimensionalKill",
            "GroupApproximation.conditional_endpoint",
        )]
        if check_required_status(references, status_requirement):
            print("self-test: exact conditional status was not recognized", file=sys.stderr)
            return 1
        wrong_status = [(
            "equivalent", "Criterion/FiniteDimensionalKill",
            "GroupApproximation.conditional_endpoint",
        )]
        if not any("but it is" in problem
                   for problem in check_required_status(references, wrong_status)):
            print("self-test: wrong required status was accepted", file=sys.stderr)
            return 1

        tex.write_text(
            r"\leanconditional{Criterion/FiniteDimensionalKill}", encoding="utf-8"
        )
        _references, problems = validate(repo, tex)
        if not any("malformed" in problem for problem in problems):
            print("self-test: malformed conditional badge was not detected", file=sys.stderr)
            return 1

        tex.write_text(
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.map_marked_commutator_eq_one}{unexpected}",
            encoding="utf-8",
        )
        _references, problems = validate(repo, tex)
        if not any("exactly two arguments" in problem for problem in problems):
            print("self-test: third badge argument was not detected", file=sys.stderr)
            return 1

        tex.write_text(
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.missing}", encoding="utf-8"
        )
        _references, problems = validate(repo, tex)
        if not any("missing declaration" in problem for problem in problems):
            print("self-test: missing declaration was not detected", file=sys.stderr)
            return 1

        tex.write_text(
            r"\leanverified{Criterion/FiniteDimensionalKill}"
            r"{GroupApproximation.strayed}", encoding="utf-8"
        )
        _references, problems = validate(repo, tex)
        if not any("is in" in problem for problem in problems):
            print("self-test: wrong-module reference was not detected", file=sys.stderr)
            return 1

        # A badge whose module and declaration agree, but on a module the root
        # never imports: everything the older gates look at is consistent, and
        # the cited theorem is still never compiled.
        tex.write_text(
            r"\leanverified{Sofic/Stray}{GroupApproximation.strayed}",
            encoding="utf-8",
        )
        _references, problems = validate(repo, tex)
        if not any("outside the import closure" in problem for problem in problems):
            print("self-test: badge on an orphan module was accepted", file=sys.stderr)
            return 1

        tex.write_text("no links here", encoding="utf-8")
        _references, problems = validate(repo, tex)
        if not any("no Lean counterpart links" in problem for problem in problems):
            print("self-test: linkless manuscript was not detected", file=sys.stderr)
            return 1
    print("check-non-mf-refs: self-test passed")
    return 0


def _write(path: Path, source: str) -> Path:
    """Small self-test helper returning the path it writes."""
    path.write_text(source, encoding="utf-8")
    return path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--decls", type=Path, default=DEFAULT_DECLS)
    parser.add_argument("--check-decls", action="store_true")
    parser.add_argument("--write-decls", action="store_true")
    parser.add_argument(
        "--extra-declarations-from", action="append", type=Path, default=[],
        help=("include declarations named by a numbered-claim JSON manifest "
              "in the generated signature roster"),
    )
    parser.add_argument(
        "--require-verified", action="append", nargs=2,
        metavar=("MODULE", "DECLARATION"), default=[],
        help="require an unconditional verified citation of one exact endpoint",
    )
    parser.add_argument(
        "--require-status", action="append", nargs=3,
        metavar=("STATUS", "MODULE", "DECLARATION"), default=[],
        help="require a citation carrying exactly the named certification status",
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()

    tex = args.tex if args.tex.is_absolute() else REPO / args.tex
    decls = args.decls if args.decls.is_absolute() else REPO / args.decls
    references, problems = validate(REPO, tex)
    problems.extend(check_required_verified(references, args.require_verified))
    invalid_statuses = [entry for entry in args.require_status
                        if entry[0] not in STATUSES]
    for status, _module, _declaration in invalid_statuses:
        problems.append(
            f"invalid required status `{status}`; expected one of {', '.join(STATUSES)}"
        )
    problems.extend(check_required_status(
        references,
        [tuple(entry) for entry in args.require_status
         if entry[0] in STATUSES],
    ))

    rendered_names = set(render_declarations(references).splitlines())
    for manifest_arg in args.extra_declarations_from:
        manifest_path = (manifest_arg if manifest_arg.is_absolute()
                         else REPO / manifest_arg)
        try:
            payload = json.loads(manifest_path.read_text(encoding="utf-8"))
            for entry in payload.get("claims", []):
                for ref in entry.get("lean", []):
                    declaration = ref.get("declaration")
                    if isinstance(declaration, str) and declaration:
                        rendered_names.add(
                            declaration if declaration.startswith("GroupApproximation.")
                            else f"GroupApproximation.{declaration}")
        except (OSError, json.JSONDecodeError, AttributeError) as error:
            problems.append(
                f"cannot read declaration manifest {manifest_path}: {error}"
            )
    rendered = "\n".join(sorted(rendered_names)) + "\n"
    if args.write_decls:
        decls.parent.mkdir(parents=True, exist_ok=True)
        decls.write_text(rendered, encoding="utf-8")
    if args.check_decls:
        if not decls.is_file():
            problems.append(f"missing generated declaration roster {decls.relative_to(REPO)}")
        elif decls.read_text(encoding="utf-8") != rendered:
            problems.append(
                f"stale generated declaration roster {decls.relative_to(REPO)}; "
                "run `python3 scripts/check_non_mf_refs.py --write-decls`"
            )

    if problems:
        print(f"check-non-mf-refs: {len(problems)} problem(s):", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    counts = {status: sum(ref.status == status for ref in references)
              for status in STATUSES}
    summary = ", ".join(
        f"{counts[status]} {status}" for status in STATUSES if counts[status]
    )
    print(
        f"check-non-mf-refs: {summary} references all resolve"
    )
    if args.write_decls:
        print(f"wrote {decls.relative_to(REPO)} ({len(set(rendered.splitlines()))} declarations)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
