#!/usr/bin/env python3
"""Validate every visible Lean counterpart link in the property-(TT)/T manuscript.

The main manuscript uses a richer ``\\leanmod`` syntax.  The property-(TT)/T
paper uses the smaller

    \\leanverified{PropertyTT/PaperStatements}{PropertyTTPaper.theorem}

surface for its visible per-result links, so this checker resolves it against the same
lexical Lean declaration index used by ``check_lean_refs.py``.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check import orphan_paths
from lean_decls import build_index


REPO = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO / "property_tt_leavitt.tex"
REFERENCE_RE = re.compile(r"\\leanverified\{([^{}]+)\}\{([^{}]+)\}")
RESULT_RE = re.compile(
    r"\\begin\{(mainthm|theorem|proposition|lemma|corollary)\}(.*?)"
    r"\\end\{\1\}",
    re.DOTALL,
)


def validate(repo: Path, tex: Path) -> list[str]:
    source = tex.read_text(encoding="utf-8")
    references = REFERENCE_RE.findall(source)
    if not references:
        return [f"no visible Lean counterpart links found in {tex.name}"]

    index = build_index(repo)
    problems: list[str] = []
    for result in RESULT_RE.finditer(source):
        if not REFERENCE_RE.search(result.group(2)):
            line = source.count("\n", 0, result.start()) + 1
            problems.append(
                f"numbered {result.group(1)} at line {line} has no Lean reference"
            )
    # A badge over a module outside the root's import closure certifies
    # nothing: `lake build` never compiles it, `#print axioms` never reaches
    # it, and the kernel audit never sees it, yet the badge renders exactly
    # like one over a verified endpoint.  Fail closed -- an unavailable
    # closure certifies nothing rather than everything.
    try:
        orphans = orphan_paths(repo)
    except OSError as error:
        orphans = None
        problems.append(
            f"cannot compute the import closure, so no badge can be certified: {error}"
        )
    for module, declaration in references:
        expected = repo / "GroupApproximation" / f"{module}.lean"
        full_name = (declaration if declaration.startswith("GroupApproximation.")
                     else f"GroupApproximation.{declaration}")
        actual = index.get(full_name)
        if orphans is not None and module in orphans:
            problems.append(
                f"badge cites GroupApproximation/{module}.lean, which is outside the "
                "import closure of GroupApproximation.lean; `lake build` never "
                f"compiles it and no audit ever sees {full_name}, so the badge "
                "certifies nothing"
            )
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
        module = repo / "GroupApproximation" / "PropertyTT"
        module.mkdir(parents=True)
        (module / "PaperStatements.lean").write_text(
            "namespace GroupApproximation\n"
            "namespace PropertyTTPaper\n"
            "theorem endpoint : True := by trivial\n"
            "end PropertyTTPaper\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        (module / "Unbuilt.lean").write_text(
            "namespace GroupApproximation\n"
            "namespace PropertyTTPaper\n"
            "theorem unbuilt : True := by trivial\n"
            "end PropertyTTPaper\n"
            "end GroupApproximation\n",
            encoding="utf-8",
        )
        # The root imports only `PaperStatements`, so `Unbuilt` is a genuine
        # orphan here and calibrates the closure gate in both directions.
        (repo / "GroupApproximation.lean").write_text(
            "import GroupApproximation.PropertyTT.PaperStatements\n",
            encoding="utf-8",
        )
        tex = repo / "paper.tex"
        tex.write_text(
            r"\leanverified{PropertyTT/PaperStatements}{PropertyTTPaper.endpoint}",
            encoding="utf-8",
        )
        if validate(repo, tex):
            print("self-test: valid reference was rejected", file=sys.stderr)
            return 1
        tex.write_text(
            r"\leanverified{PropertyTT/Unbuilt}{PropertyTTPaper.unbuilt}",
            encoding="utf-8",
        )
        if not any("outside the import closure" in problem
                   for problem in validate(repo, tex)):
            print("self-test: badge on an orphan module was accepted", file=sys.stderr)
            return 1
        tex.write_text(
            r"\leanverified{PropertyTT/PaperStatements}{PropertyTTPaper.missing}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("missing declaration" in problem for problem in problems):
            print("self-test: missing declaration was not detected", file=sys.stderr)
            return 1
        tex.write_text(
            r"\begin{theorem}Unmarked.\end{theorem}"
            r"\leanverified{PropertyTT/PaperStatements}{PropertyTTPaper.endpoint}",
            encoding="utf-8",
        )
        problems = validate(repo, tex)
        if not any("has no Lean reference" in problem for problem in problems):
            print("self-test: unmarked result was not detected", file=sys.stderr)
            return 1
    print("check-property-tt-refs: self-test passed")
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
        print(f"check-property-tt-refs: {len(problems)} problem(s):", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    count = len(REFERENCE_RE.findall(tex.read_text(encoding="utf-8")))
    print(f"check-property-tt-refs: {count} references all resolve")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
