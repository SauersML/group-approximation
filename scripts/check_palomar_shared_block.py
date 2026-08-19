#!/usr/bin/env python3
"""Gate the Palomar submission surface.

Three defects are invisible in a green `lake build` and each of them makes the
registry submission certify something other than what it appears to:

1. **The shared block drifts.**  `leanprover/comparator` compares the exported
   challenge and solution statements SYNTACTICALLY, and then walks every
   constant the statement mentions, requiring each to be identical in both
   environments.  So the definitions the statement is built from cannot be
   shared by an import; they are copied.  A copy that drifts does not fail the
   build -- both files still compile -- it fails at submission time, after the
   commit is public.

2. **The challenge acquires a project-local import.**  The registry
   recompiles `Challenge.lean` against a frozen canonical Mathlib and rejects
   any source outside Lean core, Mathlib, Tau Ceti and CSLib in its transitive
   import closure.  One `import GroupApproximation...` added for convenience
   turns the submission into a mechanical failure.

3. **The configuration stops naming the files.**  `comparator.json` names
   modules, not paths; a rename that updates the lakefile and not the JSON
   leaves a config that resolves to nothing.

4. **The compared theorem's signature drifts.**  The shared block holds the
   definitions, but the statement itself is written out separately in each
   file -- the challenge ends it with a hole and the solution with a proof --
   so nothing in the block check covers it.  Two statements that differ by a
   hypothesis compile perfectly well and are caught only by Comparator, which
   is to say only after submission.

5. **`formalization.yaml` drifts out of the registry's mechanical minimum.**
   The registry enforces a shape this repository has no other reason to
   respect -- at most two arXiv classes, a nonempty `project.description`
   which is the published abstract, and a source list that declares exactly
   one result origin.  A well-meant edit that adds a third arXiv class, or
   gives a background source a `formalizes` relationship, turns an original
   result into a contradictory one and fails intake.  Checked here only when
   PyYAML is importable; skipped, loudly, when it is not.

Run: `python3 scripts/check_palomar_shared_block.py`.  Exit 0 clean, 1 on any
finding.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CHALLENGE = REPO / "Palomar" / "Challenge.lean"
SOLUTION = REPO / "Palomar" / "Solution.lean"
CONFIG = REPO / "Palomar" / "comparator.json"

BEGIN = "-- BEGIN SHARED BLOCK"
END = "-- END SHARED BLOCK"

# Every import the challenge is allowed to name.  The registry's rule is
# "Lean core, Mathlib, Tau Ceti or CSLib"; this development uses Mathlib only,
# so anything else is a finding here rather than a surprise there.
ALLOWED_CHALLENGE_IMPORT = re.compile(r"^import\s+Mathlib(\.[A-Za-z0-9_']+)*\s*$")

IMPORT = re.compile(r"^import\s+\S+")


def fail(msg: str) -> None:
    print(f"::error::[palomar] {msg}")


def shared_block(path: Path) -> list[str] | None:
    lines = path.read_text(encoding="utf-8").splitlines()
    try:
        start = next(i for i, l in enumerate(lines) if l.startswith(BEGIN))
        stop = next(i for i, l in enumerate(lines) if l.startswith(END))
    except StopIteration:
        return None
    if stop <= start:
        return None
    return lines[start : stop + 1]


RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background",
                 "other"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof",
                "other"}
SUBSTANTIVE = {"formalizes", "adapts", "independently-proves"}


def signature(path: Path, short: str) -> list[str] | None:
    """The compared theorem's signature: its `theorem` line through `:= by`.

    Everything after `:= by` is the proof, which is supposed to differ; up to
    it, the two files must agree exactly, because that text is the statement
    Comparator compares.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(rf"^theorem {re.escape(short)}\b", line):
            start = i
            break
    if start is None:
        return None
    for j in range(start, len(lines)):
        if lines[j].rstrip().endswith(":= by") or lines[j].rstrip().endswith(":="):
            return lines[start : j + 1]
    return None


def check_metadata() -> int:
    """The subset of Palomar's `formalization.yaml` contract worth gating here.

    This is deliberately not a reimplementation of their verifier: it checks
    the constraints that this repository can plausibly violate by accident and
    that no other gate looks at.  Their `submission_contract.py` remains the
    authority.
    """
    try:
        import yaml  # noqa: PLC0415
    except ModuleNotFoundError:
        print("palomar: formalization.yaml NOT CHECKED -- PyYAML is not "
              "importable in this interpreter")
        return 0

    path = REPO / "formalization.yaml"
    if not path.is_file():
        fail("formalization.yaml: missing")
        return 1
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        fail("formalization.yaml: must contain one top-level mapping")
        return 1

    findings = 0
    project = data.get("project") or {}
    for key in ("name", "description"):
        if not (isinstance(project.get(key), str) and project[key].strip()):
            fail(f"formalization.yaml: project.{key} must be a nonempty string")
            findings += 1
    if isinstance(project.get("description"), str) and len(project["description"]) > 10_000:
        fail("formalization.yaml: project.description exceeds 10000 characters")
        findings += 1
    for key in ("authors", "responsible_maintainers"):
        value = project.get(key)
        if not (isinstance(value, list) and value):
            fail(f"formalization.yaml: project.{key} must be a nonempty list")
            findings += 1

    # The declared licence and the root licence file must agree.  Only the
    # repository's actual licence is recognised here; changing it is a
    # deliberate act that should also touch this line.
    if project.get("license") != "Apache-2.0":
        fail(f"formalization.yaml: project.license is {project.get('license')!r}; "
             "the root LICENSE is Apache-2.0 and the two must agree exactly")
        findings += 1
    licence = REPO / "LICENSE"
    if not (licence.is_file() and "Apache License" in licence.read_text(encoding="utf-8")):
        fail("LICENSE: not a readable Apache-2.0 licence file at the repository root")
        findings += 1

    classification = data.get("classification") or {}
    arxiv = classification.get("arxiv")
    if not (isinstance(arxiv, list) and 1 <= len(arxiv) <= 2 and len(set(arxiv)) == len(arxiv)):
        fail(f"formalization.yaml: classification.arxiv is {arxiv!r}; the registry "
             "accepts one or two distinct official arXiv classes")
        findings += 1
    msc = classification.get("msc2020")
    if not (isinstance(msc, list) and 1 <= len(msc) <= 8 and len(set(msc)) == len(msc)):
        fail(f"formalization.yaml: classification.msc2020 is {msc!r}; the registry "
             "accepts one to eight distinct MSC2020 codes")
        findings += 1

    sources = data.get("sources")
    if not (isinstance(sources, list) and sources):
        fail("formalization.yaml: sources must be a nonempty list")
        return findings + 1

    origins = 0
    substantive = 0
    for i, src in enumerate(sources):
        if not isinstance(src, dict):
            fail(f"formalization.yaml: sources[{i}] is not a mapping")
            findings += 1
            continue
        if not (isinstance(src.get("title"), str) and src["title"].strip()):
            fail(f"formalization.yaml: sources[{i}] has no nonempty title")
            findings += 1
        rel = src.get("relationship")
        if rel not in RELATIONSHIPS:
            fail(f"formalization.yaml: sources[{i}].relationship is {rel!r}; "
                 f"must be one of {sorted(RELATIONSHIPS)}")
            findings += 1
        kind = src.get("type")
        if kind is not None and kind not in SOURCE_TYPES:
            fail(f"formalization.yaml: sources[{i}].type is {kind!r}; must be "
                 f"one of {sorted(SOURCE_TYPES)} or absent")
            findings += 1
        if kind == "original-proof":
            origins += 1
            if rel != "other":
                fail(f"formalization.yaml: sources[{i}] declares the result origin "
                     f"but has relationship {rel!r}; an original-proof entry must "
                     "use `other`")
                findings += 1
        if rel in SUBSTANTIVE:
            substantive += 1

    # Exactly one of the two alternatives must hold, or intake fails with a
    # contradictory origin.
    if origins and substantive:
        fail(f"formalization.yaml: the source list declares an original result "
             f"({origins} original-proof entries) AND {substantive} substantive "
             "relationship(s); the two alternatives are exclusive")
        findings += 1
    elif not origins and not substantive:
        fail("formalization.yaml: the source list declares neither an "
             "original-proof entry nor any formalizes/adapts/"
             "independently-proves relationship, so it has no result origin")
        findings += 1

    methods = (data.get("automation") or {}).get("methods")
    if not (isinstance(methods, list) and methods
            and all(isinstance(m, dict) and str(m.get("method", "")).strip() for m in methods)):
        fail("formalization.yaml: automation.methods must be a nonempty list of "
             "mappings each carrying a nonempty `method`")
        findings += 1
    status = (data.get("review") or {}).get("status")
    if not (isinstance(status, str) and status.strip()):
        fail("formalization.yaml: review.status must be a nonempty string")
        findings += 1

    return findings


def main() -> int:
    findings = 0

    for path in (CHALLENGE, SOLUTION, CONFIG):
        if not path.is_file():
            fail(f"{path.relative_to(REPO)}: missing")
            findings += 1
    if findings:
        return 1

    # 1. the shared block
    a = shared_block(CHALLENGE)
    b = shared_block(SOLUTION)
    if a is None or b is None:
        fail("shared-block markers not found in both files; the copy cannot "
             "be checked, which is the same as it being wrong")
        findings += 1
    elif a != b:
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                fail(f"shared block diverges at block line {i + 1}: "
                     f"challenge {x!r} vs solution {y!r}")
                findings += 1
                break
        else:
            fail(f"shared block lengths differ: {len(a)} vs {len(b)} lines")
            findings += 1

    # 2. the challenge's imports
    for n, line in enumerate(CHALLENGE.read_text(encoding="utf-8").splitlines(), 1):
        if IMPORT.match(line) and not ALLOWED_CHALLENGE_IMPORT.match(line):
            fail(f"Palomar/Challenge.lean:{n}: {line.strip()} -- the challenge "
                 "may import Mathlib only; a project-local import fails "
                 "mechanical verification at the registry")
            findings += 1

    # 3. the configuration
    cfg = json.loads(CONFIG.read_text(encoding="utf-8"))
    expected = {
        "challenge_module": "Palomar.Challenge",
        "solution_module": "Palomar.Solution",
    }
    for key, want in expected.items():
        if cfg.get(key) != want:
            fail(f"comparator.json: {key} is {cfg.get(key)!r}, expected {want!r}")
            findings += 1
    permitted = cfg.get("permitted_axioms")
    if sorted(permitted or []) != sorted(["propext", "Quot.sound", "Classical.choice"]):
        fail(f"comparator.json: permitted_axioms is {permitted!r}; the registry "
             "accepts exactly the three classical axioms")
        findings += 1
    names = cfg.get("theorem_names") or []
    if not names:
        fail("comparator.json: theorem_names is empty")
        findings += 1
    for name in names:
        short = name.split(".")[-1]
        missing = False
        for path in (CHALLENGE, SOLUTION):
            text = path.read_text(encoding="utf-8")
            if not re.search(rf"^theorem {re.escape(short)}\b", text, re.MULTILINE):
                fail(f"{path.relative_to(REPO)}: does not declare `{short}`, "
                     f"which comparator.json selects as {name}")
                findings += 1
                missing = True
        if missing:
            continue
        # 4. the compared signature, which the shared-block check does not see
        sc = signature(CHALLENGE, short)
        ss = signature(SOLUTION, short)
        if sc is None or ss is None:
            fail(f"`{short}`: could not delimit the signature in both files "
                 "(no line ending in `:= by`), so it cannot be compared")
            findings += 1
        elif sc != ss:
            for i, (x, y) in enumerate(zip(sc, ss)):
                if x != y:
                    fail(f"`{short}`: the compared signature diverges at "
                         f"line {i + 1}: challenge {x!r} vs solution {y!r}")
                    findings += 1
                    break
            else:
                fail(f"`{short}`: the compared signature is {len(sc)} lines in "
                     f"the challenge and {len(ss)} in the solution")
                findings += 1

    findings += check_metadata()

    if findings:
        print(f"palomar: {findings} finding(s)")
        return 1
    print("palomar: shared block identical, challenge imports Mathlib only, "
          "configuration resolves, metadata meets the registry minimum")
    return 0


if __name__ == "__main__":
    sys.exit(main())
