#!/usr/bin/env python3
"""Source-text half of the validation, borrowed in shape from gnomon's
``proofs/validation/code/check.py``.

The source text and the elaborated environment are different objects and each
sees what the other cannot, which is why this file and ``scripts/Audit.lean``
both exist and neither subsumes the other:

  * this scan names the line a person typed, sees comments and docstrings, and
    -- decisively -- sees files that are never compiled at all;
  * the Lean scan sees the premises the kernel actually inserted and the
    transitive axiom closure, none of which exists in the source text.

Every check here is calibrated in BOTH directions by ``--self-test``: each
planted defect must be reported, and a clean tree must be silent.  A detector
that reports nothing is otherwise indistinguishable from a clean corpus, which
is the failure mode this whole directory exists to avoid.

    python3 scripts/check.py             # gate; nonzero exit on any finding
    python3 scripts/check.py --self-test # calibration; run first in CI
"""

from __future__ import annotations

import argparse
import os
import re
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LIB = "GroupApproximation"

# Every Lean library in the repository.  Dead and superseded developments are
# deleted rather than kept behind an unbuilt compatibility root.
LIBS = (LIB,)

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
NATIVE_DECIDE_RE = re.compile(
    r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])")
ADMIT_RE = re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])")
ESCAPE_HATCH_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:unsafe|implemented_by|opaque)(?![A-Za-z0-9_])")

sys.path.insert(0, str(Path(__file__).resolve().parent))
import claim_map  # noqa: E402  (path set above)

# Each entry is (label, compiled regex).  Matches are reported with file:line.
#
# `sorry` is scanned here AND caught by the kernel audit as `sorryAx`.  That is
# deliberate duplication: a `sorry` in a module outside the import closure is
# invisible to the kernel scan, and a `sorry` reached through a macro is
# invisible to this one.
FORBIDDEN = [
    ("sorry / sorryAx", re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])|sorryAx")),
    ("admit", ADMIT_RE),
    ("hand-declared axiom", re.compile(r"^[ \t]*axiom[ \t]", re.MULTILINE)),
    ("native_decide (trusts the compiler, not the kernel)", NATIVE_DECIDE_RE),
    ("unsafe / implemented_by / opaque escape hatch", ESCAPE_HATCH_RE),
    ("warningAsError disabled", re.compile(r"warningAsError[ \t]*(:=)?[ \t]*false")),
    # Any value, not just 0: `maxHeartbeats 400000` and `maxHeartbeats 0` differ
    # only in how long the same unfixed proof is allowed to flail.  A timeout is
    # a statement about the proof -- a `whnf` that unfolds something that should
    # be irreducible, a `simp` set that should be a `rw`, a `decide` that should
    # be a lemma -- and the fix is the cheaper proof, not the larger budget.
    # `synthInstance.maxHeartbeats` and friends are caught by the same rule.
    ("maxHeartbeats budget bump",
     re.compile(r"set_option[ \t]+([A-Za-z0-9_]+\.)*maxHeartbeats(?![A-Za-z0-9_])")),
    # A recursion-depth override is the same kind of proof-budget escape as a
    # heartbeat override: it can make an accidentally enormous reduction
    # elaborate without repairing its proof structure.  Exact generated
    # certificates must instead be split into kernel-checkable pieces.
    ("maxRecDepth budget bump",
     re.compile(r"set_option[ \t]+([A-Za-z0-9_]+\.)*maxRecDepth(?![A-Za-z0-9_])")),
]

# The environment-scan calibration corpus must contain one real defect.  This
# is the only exception to the repository-wide lexical prohibition, pinned to
# its exact path, line, tag, and source text so it cannot become a general
# escape hatch.
FORBIDDEN_ALLOWLIST = {
    ("hand-declared axiom", "scripts/Audit/Plants.lean", 28,
     "axiom plantedAxiom : True"),
}

# Strings known to have been fabricated in earlier edits and purged from the
# publication surface (see docs/ADVERSARIAL_AUDIT_NON_MF_2026-08-13.md).  The
# "Leiden Declaration" and its Zenodo DOI do not exist; the reference was
# purged once and reintroduced by a later merge, so it is gated here.  The
# gate covers publication-facing files only: audit records under docs/
# legitimately discuss these strings when recording the purges.
FABRICATED = [
    ("fabricated citation (Leiden Declaration)",
     re.compile(r"Leiden\s+Declaration", re.IGNORECASE)),
    ("fabricated citation (Leiden Declaration)",
     re.compile(r"zenodo\.20302944")),
]


# There are no budgets: any finding, under any tag, fails the run.  Nothing is
# report-only and nothing is a ratchet, so there is no number a reviewer can
# raise instead of fixing the source, and a scan cannot be quietened by editing
# this file.  The roster below is for reporting only -- a passing run prints a
# count for every detector, since a scan that has silently stopped firing is
# otherwise indistinguishable from a clean tree -- and a finding under a tag
# missing from it fails just the same.
SCAN_TAGS: tuple[str, ...] = (
    "orphan module",
    "sorry / sorryAx",
    "admit",
    "hand-declared axiom",
    "native_decide (trusts the compiler, not the kernel)",
    "unsafe / implemented_by / opaque escape hatch",
    "warningAsError disabled",
    "maxHeartbeats budget bump",
    "maxRecDepth budget bump",
    "unmapped result",
    "dangling Lean reference",
    "dangling Lean reference (wrapped note)",
    "axiom-report pinning",
    "stale generated claim map",
    "status contract",
)


class Findings:
    def __init__(self) -> None:
        self.rows: list[tuple[str, str]] = []
        # A detector that cannot run on this tree prints why instead of `0`.
        # Printing `0` for a scan that never executed is the exact failure the
        # roster above exists to prevent: it reads as "checked and clean".
        self.skipped: dict[str, str] = {}

    def add(self, tag: str, detail: str) -> None:
        self.rows.append((tag, detail))

    def skip(self, tag: str, reason: str) -> None:
        self.skipped[tag] = reason

    def report(self, stream=sys.stdout) -> int:
        counts: dict[str, int] = {}
        for tag, _ in self.rows:
            counts[tag] = counts.get(tag, 0) + 1
        for tag, detail in self.rows:
            print(f"::error::[{tag}] {detail}", file=stream)
        for tag in SCAN_TAGS:
            if tag in self.skipped and not counts.get(tag, 0):
                print(f"{tag}: NOT RUN -- {self.skipped[tag]}", file=stream)
            else:
                print(f"{tag}: {counts.get(tag, 0)}", file=stream)
        for tag, count in sorted(counts.items()):
            if tag not in SCAN_TAGS:
                print(f"{tag}: {count} (tag not on the roster)", file=stream)
        return 1 if self.rows else 0


def module_files(root: Path, lib: str = LIB) -> dict[str, Path]:
    """Module name -> path, for every ``.lean`` file under ``lib``."""
    out = {}
    lib_root = root / f"{lib}.lean"
    if lib_root.exists():
        out[lib] = lib_root
    if (root / lib).is_dir():
        for p in sorted((root / lib).rglob("*.lean")):
            rel = p.relative_to(root).with_suffix("")
            out[".".join(rel.parts)] = p
    return out


def all_module_files(root: Path) -> dict[str, Path]:
    """Every module of every library in the repository."""
    out: dict[str, Path] = {}
    for lib in LIBS:
        out.update(module_files(root, lib))
    return out


def lean_source_files(root: Path) -> list[Path]:
    """Every Lean source physically present under ``root`` and subject to the scan.

    The excluded directories are pruned during the walk, not filtered after it.
    `rglob` descends into `.lake` -- the whole of Mathlib -- to discard every
    file it finds there, and a `lake build` running concurrently deletes lock
    directories underneath it, which crashed this scan with `FileNotFoundError`
    instead of reporting anything.
    """
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
        out.extend(Path(dirpath) / name for name in filenames
                   if name.endswith(".lean"))
    return sorted(out)


def import_closure(modules: dict[str, Path], start: str) -> set[str]:
    """Modules reachable from ``start`` by following imports within its library."""
    lib = start.split(".", 1)[0]
    seen: set[str] = set()
    stack = [start]
    while stack:
        m = stack.pop()
        if m in seen or m not in modules:
            continue
        seen.add(m)
        text = modules[m].read_text(encoding="utf-8", errors="replace")
        for imp in IMPORT_RE.findall(text):
            if imp == lib or imp.startswith(lib + "."):
                stack.append(imp)
    return seen


def orphan_modules(root: Path) -> set[str]:
    """Every module outside its library root's import closure, by dotted name.

    Raises rather than returning an empty set when a library root is missing:
    "no orphans" and "I could not tell" are the same value but opposite facts,
    and the callers gate publication on the answer.  A badge checker that
    silently degraded to "no orphans" would certify exactly the modules this
    is meant to catch.
    """
    orphans: set[str] = set()
    for lib in LIBS:
        modules = module_files(root, lib)
        if not modules:
            continue
        if lib not in modules:
            raise FileNotFoundError(f"root module {lib}.lean not found under {root}")
        reachable = import_closure(modules, lib)
        orphans.update(name for name in modules if name not in reachable)
    return orphans


def orphan_paths(root: Path) -> set[str]:
    """`orphan_modules` in the slash-separated form the manuscript badges use.

    A badge names `Sofic/LiteralNonMFEndpoint`, not the dotted module, and both
    badge checkers need the comparison; translating once here keeps them from
    each growing their own version of it.
    """
    return {"/".join(name.split(".")[1:]) for name in orphan_modules(root)}


def check_import_closure(root: Path, f: Findings) -> None:
    """Every library module must be reachable from the root module.

    This is not a tidiness check.  ``lake build`` builds the root module's
    import closure, so a module nothing imports is NEVER COMPILED: it can be
    broken, contain a `sorry`, or contradict the rest of the development, and
    both a green build and the kernel audit will agree that everything is fine,
    because neither ever loaded it.  An orphan is therefore either a missing
    import or dead code to delete, and the repository cannot tell you which.
    """
    for lib in LIBS:
        modules = module_files(root, lib)
        if not modules:
            continue
        if lib not in modules:
            f.add("import closure", f"root module {lib}.lean not found")
            continue
        reachable = import_closure(modules, lib)
        for name in sorted(modules):
            if name not in reachable:
                rel = modules[name].relative_to(root)
                f.add("orphan module",
                      f"{rel}: not in the import closure of {lib}.lean, so `lake build` "
                      f"never compiles it and no audit ever sees it")


def _mask_lean_comments(text: str) -> str:
    """Replace Lean comments by spaces, preserving offsets and newlines.

    `admit`, `unsafe`, `opaque`, and `implemented_by` are ordinary English or
    audit vocabulary too, so their prohibition is on executable source tokens,
    not prose.  Lean block comments nest; preserving every character position
    keeps the source-line reporting below exact.
    """
    out = list(text)
    depth = 0
    i = 0
    while i < len(text):
        # A comment opener inside a string is data, not syntax.  Leave string
        # contents visible to the conservative token scan, but skip over them
        # while locating comments so a value such as `"/-"` cannot mask the
        # executable source that follows it.
        if depth == 0 and text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += min(2, len(text) - i)
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        if depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and text[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


CODE_TOKEN_TAGS = {
    "admit",
    "unsafe / implemented_by / opaque escape hatch",
}


def check_forbidden(root: Path, f: Findings) -> None:
    # Scan every Lean source, including standalone audits, generated probes,
    # and files outside the import closure.  A clean build cannot certify code
    # it never imports, but the source prohibition still applies there.
    for path in lean_source_files(root):
        text = path.read_text(encoding="utf-8", errors="replace")
        code_text = _mask_lean_comments(text)
        rel = path.relative_to(root)
        for label, pattern in FORBIDDEN:
            searched = code_text if label in CODE_TOKEN_TAGS else text
            for m in pattern.finditer(searched):
                line = text.count("\n", 0, m.start()) + 1
                source_line = text.splitlines()[line - 1].strip()
                key = (label, str(rel), line, source_line)
                if key not in FORBIDDEN_ALLOWLIST:
                    f.add(label, f"{rel}:{line}: {source_line}")


# The "stale conditionality disclaimer" scan used to live here.  It moved to
# `Audit.Scan` as STALE_DISCLAIMER, because the question it asks is not
# answerable in the source text: a docstring saying "conditional on the
# rose-graph `K1` input" is CORRECT when the theorem takes that input as a
# hypothesis, and this file cannot see the hypothesis.  Its only findings on
# this corpus were four such sentences, every one of them true, so its only
# green state was one where accurate documentation had been deleted.
#
# The environment sees the docstring AND the type, so the scan is decidable
# there and sharper: conditionality prose on a statement with no Prop premise.
# What no longer gets checked anywhere: module docstrings (`/-! ... -/`), which
# belong to no declaration.  One of the original four was exactly that.

def check_fabricated_citations(root: Path, f: Findings) -> None:
    """Publication-facing files must not cite known-fabricated references."""
    candidates = sorted(root.glob("*.tex"))
    for name in ("README.md", "CITATION.cff"):
        p = root / name
        if p.is_file():
            candidates.append(p)
    for path in candidates:
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in FABRICATED:
            for m in pattern.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                f.add(label,
                      f"{path.name}:{line}: {text.splitlines()[line - 1].strip()}")


# The detectors that have no source once the manuscript is gone.  `dangling
# Lean reference` is deliberately absent: the frozen roster still names
# declarations, so that one keeps running against the roster below.
_MANUSCRIPT_ONLY_TAGS = (
    "unmapped result",
    "dangling Lean reference (wrapped note)",
    "axiom-report pinning",
    "stale generated claim map",
    "status contract",
)


def check_frozen_claim_roster(root: Path, f: Findings) -> None:
    """A claim map whose manuscript is missing still has to name real declarations.

    `metadata/CLAIM_DECLS.txt` is the list `scripts/Signatures.lean` elaborates and
    pins in `metadata/CLAIM_SIGNATURES.md`, so a name that leaves the library must
    not leave this roster behind -- and with no manuscript to regenerate from,
    the roster can only be checked, not rebuilt.  Nothing here can tell whether
    the roster still *covers* what it should; only that what it lists exists.
    This is the degraded mode: it exists so that losing the manuscript is loud.
    """
    decls = root / claim_map.GENERATED_DECLS
    generated = root / claim_map.GENERATED
    if not decls.is_file() and not generated.is_file():
        return

    reason = (f"{claim_map.TEX_NAME} is not in the tree; the roster it generated "
              f"is frozen and cannot be regenerated or diffed")
    for tag in _MANUSCRIPT_ONLY_TAGS:
        f.skip(tag, reason)
    if not decls.is_file():
        f.add("dangling Lean reference",
              f"{claim_map.GENERATED} is present but {claim_map.GENERATED_DECLS}, "
              f"the roster `scripts/Signatures.lean` reads, is not")
        return

    index = claim_map.build_index(root)
    for line_number, line in enumerate(
            decls.read_text(encoding="utf-8").splitlines(), start=1):
        name = line.strip()
        if name and name not in index:
            f.add("dangling Lean reference",
                  f"{claim_map.GENERATED_DECLS}:{line_number}: `{name}` is pinned "
                  f"by the frozen claim roster but the library no longer declares it")


def check_claim_map(root: Path, f: Findings) -> None:
    """The paper's margin notes must name declarations that exist.

    The manuscript asserts, on each numbered result, which Lean declarations
    formalize it.  Nothing about editing either side keeps that true: rename a
    theorem and the paper goes on pointing at it, in a PDF that still compiles
    and a library that still builds.  Only a scan that reads both can tell.

    Three ways it can be wrong, and all three are findings:

      * a result states something the paper never claims is formalized -- the
        note is simply missing, so the reader cannot tell whether that is a gap
        in the formalization or a gap in the bookkeeping;
      * a note names a module or declaration the library does not contain;
      * the set of cited modules outside the `#audit_axioms` report drifts from
        the set pinned in `claim_map`, so the paper's audit story quietly stops
        describing the audit that actually runs.

    When the manuscript is not in the tree none of that can run.  This scan
    used to return early there, silently: the manuscript it reads was deleted
    on 2026-08-12 by a commit whose message never mentioned it, and for four
    days five detectors printed `0` while executing nothing.  A missing
    manuscript is now reported as such, and `check_frozen_claim_roster` checks
    the half of the contract that survives it -- that every name in the roster
    `scripts/Signatures.lean` elaborates still exists.
    """
    tex = root / claim_map.TEX_NAME
    if not tex.is_file():
        check_frozen_claim_roster(root, f)
        return

    claims = claim_map.read_claims(tex)

    for claim in claims:
        if claim.env in claim_map.RESULT_ENVS and claim.status is None:
            f.add("unmapped result",
                  f"{tex.name}:{claim.line}: `{claim.label}` ({claim.env}) carries no "
                  f"Lean note, so the paper neither claims it is formalized nor says "
                  f"it is not")

    # A "verified" badge must not narrate its own boundary: a note that says
    # part of the result remains prose belongs on a \leanpartial, where the
    # explanation is the second argument.  Without this, the status vocabulary
    # decays into one green color regardless of what the notes admit.
    _CONTRACT = re.compile(r"remains? (?:a )?(?:paper|prose)|not formali[sz]ed|"
                           r"unformali[sz]ed", re.I)
    for claim in claims:
        if claim.status == "verified" and _CONTRACT.search(claim.note or ""):
            f.add("status contract",
                  f"{tex.name}:{claim.line}: `{claim.label}` is marked verified "
                  f"but its note admits an unformalized remainder; use "
                  f"\\leanpartial and say exactly what is covered")

    _, problems = claim_map.resolve(claims, root)
    wrapped = {c.label for c in claims if c.status and c.wrapped}
    for problem in problems:
        # Labels contain colons, so the label is recognised by prefix rather
        # than by splitting on the first one.
        tag = ("dangling Lean reference (wrapped note)"
               if any(problem.startswith(f"{label}:") for label in wrapped)
               else "dangling Lean reference")
        f.add(tag, f"{tex.name}: {problem}")

    # Pinned only against the real corpus; the synthetic tree used by
    # --self-test has its own, empty, expectation.
    expected = (claim_map.CITED_OUTSIDE_AXIOM_REPORT
                if root == REPO else frozenset())
    closure = claim_map.audit_report_closure(root)
    # Notes may name a module by path; the closure is keyed by basename, which
    # is what identifies a module regardless of which directory it sits in.
    cited = {m.rsplit("/", 1)[-1] for c in claims for m, _ in c.blocks}
    actual = frozenset(m for m in cited if m not in closure)
    for module in sorted(actual - expected):
        f.add("axiom-report pinning",
              f"{module} is cited by the paper but is outside the import closure of "
              f"{LIB}/Endpoint/Audit.lean, and is not pinned in "
              f"claim_map.CITED_OUTSIDE_AXIOM_REPORT")
    for module in sorted(expected - actual):
        f.add("axiom-report pinning",
              f"{module} is pinned in claim_map.CITED_OUTSIDE_AXIOM_REPORT but is no "
              f"longer both cited and outside the {LIB}/Endpoint/Audit.lean closure; "
              f"the pin is stale")

    # The committed table is a build product.  Checking it here is what makes
    # it safe for the README to point at instead of restating: a table nobody
    # regenerates is exactly the hand-maintained table this replaced.
    generated = root / claim_map.GENERATED
    if generated.is_file():
        if generated.read_text(encoding="utf-8") != claim_map.render(root):
            f.add("stale generated claim map",
                  f"{claim_map.GENERATED} no longer matches the manuscript and the "
                  f"library; regenerate it with `python3 scripts/claim_map.py --write`")
        # The declaration list feeds `scripts/Signatures.lean`; if it drifts,
        # the signature file pins the types of yesterday's mapping.
        decls = root / claim_map.GENERATED_DECLS
        if not decls.is_file() or \
                decls.read_text(encoding="utf-8") != claim_map.render_decls(root):
            f.add("stale generated claim map",
                  f"{claim_map.GENERATED_DECLS} no longer matches the manuscript and "
                  f"the library; regenerate it with `python3 scripts/claim_map.py --write`")


CHECKS = [
    ("import closure", check_import_closure),
    ("claim map", check_claim_map),
    ("forbidden constructs", check_forbidden),
    ("fabricated citations", check_fabricated_citations),
]


def run(root: Path) -> Findings:
    f = Findings()
    for _, fn in CHECKS:
        fn(root, f)
    return f


# --------------------------------------------------------------------------
# Calibration.  Both directions, because a silent detector and a clean corpus
# look identical from the outside.
# --------------------------------------------------------------------------

# The claim-map detectors read a manuscript as well as a library, so the
# synthetic corpus carries a miniature of each: one result, one margin note,
# and an `Endpoint.Audit` module whose import closure the note's module lies inside.
_TEX = claim_map.TEX_NAME

CLEAN_TREE = {
    f"{LIB}.lean":
        f"import {LIB}.Alpha\nimport {LIB}.Beta\nimport {LIB}.Endpoint.Audit\n",
    f"{LIB}/Alpha.lean": "theorem alpha : True := trivial\n",
    f"{LIB}/Beta.lean":
        f"import {LIB}.Alpha\n-- an ordinary comment that claims nothing\n"
        "-- Groups admit models; audit prose may say unsafe, opaque, or implemented_by.\n"
        "def commentMarker : String := \"/-\"\n"
        "theorem beta : True := trivial\n",
    f"{LIB}/Endpoint/Audit.lean": f"import {LIB}.Alpha\n#audit_axioms alpha\n",
    _TEX: (
        "\\begin{lemma}\\label{lem:demo}%\n"
        "\\leanverified{\\leanmod{Alpha}{alpha}}%\n"
        "A statement.\n"
        "\\end{lemma}\n"
    ),
}

PLANTS = [
    ("orphan module", {f"{LIB}/Orphan.lean": "theorem orphan : False := by sorry\n"}),
    ("sorry / sorryAx", {f"{LIB}/Alpha.lean": "theorem alpha : True := by sorry\n"}),
    ("admit", {f"{LIB}/Alpha.lean": "theorem alpha : True := by admit\n"}),
    ("admit", {f"{LIB}/Alpha.lean": "theorem alpha : True := by\n  admit\n"}),
    ("hand-declared axiom",
     {f"{LIB}/Alpha.lean": "-- declaration below the first line\naxiom alpha : True\n"}),
    ("native_decide (trusts the compiler, not the kernel)",
     {"scripts/Standalone.lean": "theorem standalone : True := by native_decide\n"}),
    ("unsafe / implemented_by / opaque escape hatch",
     {f"{LIB}/Alpha.lean": "unsafe def alpha : Nat := 0\n"}),
    ("unsafe / implemented_by / opaque escape hatch",
     {f"{LIB}/Alpha.lean":
      "def commentMarker : String := \"/-\"\nprivate unsafe def alpha : Nat := 0\n"}),
    ("unsafe / implemented_by / opaque escape hatch",
     {f"{LIB}/Alpha.lean": "opaque alpha : Nat\n"}),
    ("unsafe / implemented_by / opaque escape hatch",
     {f"{LIB}/Alpha.lean": "private opaque alpha : Nat\n"}),
    ("unsafe / implemented_by / opaque escape hatch",
     {f"{LIB}/Alpha.lean": "@[implemented_by alphaImpl] def alpha : Nat := 0\n"}),
    ("unsafe / implemented_by / opaque escape hatch",
     {f"{LIB}/Alpha.lean": "@[ implemented_by alphaImpl] def alpha : Nat := 0\n"}),
    ("warningAsError disabled",
     {f"{LIB}/Alpha.lean": "set_option warningAsError false\n"}),
    # A raise, not `0`: the plant is the case the old `maxHeartbeats 0` regex
    # walked straight past, so it fails against the detector it replaced.
    ("maxHeartbeats budget bump",
     {f"{LIB}/Alpha.lean":
      "set_option maxHeartbeats 400000 in\ntheorem a : True := trivial\n"}),
    ("maxRecDepth budget bump",
     {f"{LIB}/Alpha.lean":
      "set_option maxRecDepth 20000 in\ntheorem a : True := trivial\n"}),
    # A result the paper states and never says anything about: the reader
    # cannot distinguish "not formalized" from "nobody wrote the note".
    ("unmapped result",
     {_TEX: "\\begin{theorem}\\label{thm:silent}%\nA statement.\n\\end{theorem}\n"}),
    # A note that points at a declaration the library does not have -- what a
    # rename on the Lean side leaves behind.
    ("dangling Lean reference",
     {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
             "\\leanverified{\\leanmod{Alpha}{alpha_renamed_away}}%\n"
             "A statement.\n\\end{lemma}\n")}),
    # A note wrapped across lines.  Before brace-balanced parsing this lost
    # every \leanmod after the newline silently, so the reference below went
    # unchecked rather than reported.
    ("dangling Lean reference (wrapped note)",
     {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
             "\\leanverified{\\leanmod{Alpha}{alpha}%\n"
             "\\leanmod{Alpha}{alpha_renamed_away}}%\n"
             "A statement.\n\\end{lemma}\n")}),
    # The committed table left behind by an edit to either side.
    ("stale generated claim map",
     {"metadata/CLAIM_MAP.md": "# TeX map\n\nstale contents\n"}),
    # A green badge whose own note admits a prose remainder.
    ("status contract",
     {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
             "\\leanverified{\\leanmod{Alpha}{alpha}"
             "\\leannote{the second half remains prose.}}%\n"
             "A statement.\n\\end{lemma}\n")}),
    # A citation of a module the axiom report never reaches, unpinned.
    ("axiom-report pinning",
     {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
             "\\leanverified{\\leanmod{Beta}{beta}}%\n"
             "A statement.\n\\end{lemma}\n")}),
    # The fabricated reference that was purged once and came back in a merge.
    ("fabricated citation (Leiden Declaration)",
     {"README.md": "In the spirit of the Leiden Declaration (2026).\n"}),
]


def _materialize(base: Path, tree: dict[str, str]) -> None:
    for rel, text in tree.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")


def self_test() -> int:
    failures = []

    # Direction 1: a clean tree is silent.  Without this, a detector that
    # crashes or matches nothing would "pass" every plant below by accident.
    with tempfile.TemporaryDirectory() as d:
        base = Path(d)
        _materialize(base, CLEAN_TREE)
        rows = run(base).rows
        if rows:
            failures.append(f"clean tree reported {len(rows)} findings: {rows}")

    # Direction 2: every planted defect is reported, under its own tag.  The
    # tag matters: a gate that fires under the wrong label can alarm but cannot
    # localize.
    for tag, plant in PLANTS:
        with tempfile.TemporaryDirectory() as d:
            base = Path(d)
            _materialize(base, CLEAN_TREE)
            _materialize(base, plant)
            tags = {t for t, _ in run(base).rows}
            if tag not in tags:
                failures.append(f"plant {tag!r} was NOT reported (got {sorted(tags)})")

    # Direction 3: the tree this scan actually meets.  Every plant above is
    # materialized on top of a corpus that contains the manuscript, so none of
    # them exercises the path taken when the manuscript is gone -- which is the
    # live path, and the one where a detector that reports nothing would look
    # exactly like a clean corpus.
    retired = {rel: text for rel, text in CLEAN_TREE.items() if rel != _TEX}
    with tempfile.TemporaryDirectory() as d:
        base = Path(d)
        _materialize(base, retired)
        _materialize(base, {str(claim_map.GENERATED_DECLS): "alpha\n"})
        result = run(base)
        if result.rows:
            failures.append(
                f"retired tree with a resolving roster reported {result.rows}")
        for tag in _MANUSCRIPT_ONLY_TAGS:
            if tag not in result.skipped:
                failures.append(
                    f"retired tree printed {tag!r} as a count, not as not-run")

    with tempfile.TemporaryDirectory() as d:
        base = Path(d)
        _materialize(base, retired)
        _materialize(base,
                     {str(claim_map.GENERATED_DECLS): "alpha_renamed_away\n"})
        tags = {t for t, _ in run(base).rows}
        if "dangling Lean reference" not in tags:
            failures.append("a frozen roster naming a departed declaration was "
                            f"NOT reported (got {sorted(tags)})")

    for line in failures:
        print(f"::error::[calibration] {line}")
    if failures:
        return 1
    print(f"calibration: clean tree silent; {len(PLANTS)} planted defects all "
          f"reported; retired-manuscript path calibrated both ways")
    return 0


def list_orphans(root: Path) -> int:
    """Print every module outside its library root's import closure, one per line.

    `scripts/msi-build.sh` has to name the orphans as explicit build targets,
    because `lake build` reaches only the root's closure.  It used to decide
    that with its own shell test for a *direct* `import` line in the root
    module, which every transitively-reached module fails -- so a no-argument
    invocation named hundreds of targets and built the whole corpus while
    holding the fleet lock.  One closure implementation, printed here, is what
    keeps the build script and this scan from ever disagreeing again.
    """
    for name in sorted(orphan_modules(root)):
        print(name)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true",
                    help="calibrate the detectors in both directions and exit")
    ap.add_argument("--list-orphans", action="store_true",
                    help="print modules outside the root import closure and exit")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    if args.list_orphans:
        return list_orphans(REPO)
    f = run(REPO)
    status = f.report()
    n = len(lean_source_files(REPO))
    verdict = "clean" if status == 0 else "FINDINGS"
    print(f"source scan: {n} Lean sources, {len(f.rows)} findings, {verdict}")
    return status


if __name__ == "__main__":
    sys.exit(main())
