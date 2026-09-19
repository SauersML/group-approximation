#!/usr/bin/env python3
"""Gate the Palomar submission surface.

Five defects are invisible in a green `lake build`, and each of them makes the
registry submission certify something other than what it appears to:

1. **The shared block drifts.**  `leanprover/comparator` compares the exported
   challenge and solution statements SYNTACTICALLY, and then walks every
   constant the statement mentions, requiring each to be identical in both
   environments (`Comparator/Compare.lean`; the declaration-closure note in
   `PalomarSubmission/docs`).  The definitions the statement is built from
   therefore cannot be shared by an import; they are copied.  A copy that
   drifts does not fail the build -- both files still compile -- it fails at
   submission time, after the commit is public.

2. **The compared theorem's signature drifts.**  The shared block holds the
   definitions, but the statement is written out separately in each file: the
   challenge ends it with a hole, the solution with a proof.  Two signatures
   differing by a hypothesis compile perfectly well.

3. **The challenge acquires a project-local import.**  The registry recompiles
   `Challenge.lean` against a frozen canonical Mathlib and rejects any source
   outside Lean core, Mathlib, Tau Ceti and CSLib in its transitive import
   closure.  One `import GroupApproximation...` added for convenience turns the
   submission into a mechanical failure.

4. **The configuration stops naming the files.**  `comparator.json` names
   modules, not paths; a rename that updates the lakefile and not the JSON
   leaves a configuration that resolves to nothing.

5. **A mechanical prerequisite silently stops holding.**  The registry caps the
   challenge at 100 KiB and 1,000 lines, requires exactly one root licence
   file, a `lean-toolchain` naming a release at or above its minimum, every Git
   dependency pinned to a full lowercase SHA on github.com, and no compiled
   artifacts, submodules or LFS anywhere.  Each of those fails intake rather
   than review, and nothing else here looks at them.

6. **`formalization.yaml` drifts out of the registry's mechanical minimum** --
   at most two arXiv classes, a nonempty `project.description` (which is the
   published abstract), and a source list declaring exactly one result origin.
   Checked only when PyYAML is importable; skipped, loudly, when it is not.

This is deliberately NOT a reimplementation of Palomar's verifier.  It checks
the rules this repository can plausibly break by accident, in the shape the
verifier states them, and `PalomarSubmission/scripts/verify_submission.py`
remains the authority.  The one thing it cannot see is the statement as
ELABORATED -- a different instance resolved on one side, a coercion inserted on
one side -- which is what `scripts/check_palomar_statement_match.sh` compares,
after the build.

    python3 scripts/check_palomar_submission.py             # gate
    python3 scripts/check_palomar_submission.py --self-test  # calibration

CALIBRATION.  Every mechanical rule below is planted and re-checked by
`--self-test`: a detector that reports nothing on a clean tree and a detector
that has silently stopped firing look exactly the same from here.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

BEGIN = "-- BEGIN SHARED BLOCK"
END = "-- END SHARED BLOCK"

# Every constant below is the registry's, transcribed from
# `PalomarSubmission/scripts/verify_submission.py`.  They are duplicated
# deliberately: a gate that read the registry's source at runtime would only
# work on a machine that happens to have that checkout.
MAX_CHALLENGE_BYTES = 100 * 1024
MAX_CHALLENGE_LINES = 1000
PREFERRED_CHALLENGE_BYTES = 32 * 1024
PREFERRED_CHALLENGE_LINES = 300
MAX_CONFIGURATION_BYTES = 1024 * 1024
MAX_LICENSE_BYTES = 1024 * 1024
MAX_FORMALIZATION_BYTES = 256 * 1024
MINIMUM_TOOLCHAIN = (4, 28, 0)
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
COMPARATOR_REQUIRED_KEYS = {
    "challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
COMPARATOR_ALLOWED_KEYS = COMPARATOR_REQUIRED_KEYS | {
    "definition_names", "enable_nanoda"}
TOOLCHAIN_RE = re.compile(
    r"^leanprover/lean4:v(?P<major>[0-9]+)\.(?P<minor>[0-9]+)\.(?P<patch>[0-9]+)"
    r"(?:-rc(?P<rc>[0-9]+))?$")
LICENSE_FILE_RE = re.compile(
    r"^(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?$",
    re.IGNORECASE)
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
GITHUB_URL_RE = re.compile(r"^https://github\.com/[^/?#]+/[^/?#]+?(?:\.git)?$")
COMPILED_ARTIFACT_SUFFIXES = {
    ".a", ".bc", ".dll", ".dylib", ".ilean", ".ir", ".o", ".obj", ".olean",
    ".so", ".trace"}
COMPILED_ARTIFACT_NAME_SUFFIXES = (".olean.private", ".olean.server")

# The registry allows Mathlib, Tau Ceti and CSLib in a challenge's import
# closure.  This development uses Mathlib alone, so anything else is a finding
# here rather than a surprise there.
ALLOWED_CHALLENGE_IMPORT = re.compile(r"^import\s+Mathlib(\.[A-Za-z0-9_']+)*\s*$")
IMPORT = re.compile(r"^import\s+\S+")

RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background",
                 "other"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof",
                "other"}
SUBSTANTIVE = {"formalizes", "adapts", "independently-proves"}


class Findings:
    def __init__(self) -> None:
        self.rows: list[str] = []

    def add(self, message: str) -> None:
        self.rows.append(message)
        print(f"::error::[palomar] {message}")

    def note(self, message: str) -> None:
        print(f"palomar: NOTE -- {message}")


def challenge(root: Path) -> Path:
    return root / "Palomar" / "Challenge.lean"


def solution(root: Path) -> Path:
    return root / "PalomarSolution.lean"


def config_path(root: Path) -> Path:
    return root / "Palomar" / "comparator.json"


# --------------------------------------------------------------------------
# 1-4: the two files and the configuration
# --------------------------------------------------------------------------

def shared_block(path: Path) -> list[str] | None:
    lines = path.read_text(encoding="utf-8").splitlines()
    try:
        start = next(i for i, l in enumerate(lines) if l.startswith(BEGIN))
        stop = next(i for i, l in enumerate(lines) if l.startswith(END))
    except StopIteration:
        return None
    return lines[start : stop + 1] if stop > start else None


def signature(path: Path, short: str) -> list[str] | None:
    """The compared theorem's signature: its `theorem` line through `:= by`.

    Everything after that is the proof, which is supposed to differ.  Up to it,
    the two files must agree exactly: that text is the statement Comparator
    compares.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next((i for i, l in enumerate(lines)
                  if re.match(rf"^theorem {re.escape(short)}\b", l)), None)
    if start is None:
        return None
    for j in range(start, len(lines)):
        stripped = lines[j].rstrip()
        if stripped.endswith(":= by") or stripped.endswith(":="):
            return lines[start : j + 1]
    return None


def check_files(root: Path, f: Findings) -> None:
    for path in (challenge(root), solution(root), config_path(root)):
        if not path.is_file():
            f.add(f"{path.relative_to(root)}: missing")
            return

    a, b = shared_block(challenge(root)), shared_block(solution(root))
    if a is None or b is None:
        f.add("shared-block markers not found in both files; the copy cannot be "
              "checked, which is the same as it being wrong")
    elif a != b:
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                f.add(f"shared block diverges at block line {i + 1}: "
                      f"challenge {x!r} vs solution {y!r}")
                break
        else:
            f.add(f"shared block is {len(a)} lines in the challenge and {len(b)} "
                  "in the solution")

    for n, line in enumerate(
            challenge(root).read_text(encoding="utf-8").splitlines(), 1):
        if IMPORT.match(line) and not ALLOWED_CHALLENGE_IMPORT.match(line):
            f.add(f"Palomar/Challenge.lean:{n}: {line.strip()} -- the challenge "
                  "may import Mathlib only; a project-local import fails "
                  "mechanical verification at the registry")

    try:
        cfg = json.loads(config_path(root).read_text(encoding="utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        f.add("comparator.json is not valid UTF-8 JSON")
        return
    if not isinstance(cfg, dict):
        f.add("comparator.json must contain one JSON object")
        return
    missing = COMPARATOR_REQUIRED_KEYS - cfg.keys()
    if missing:
        f.add(f"comparator.json is missing {', '.join(sorted(missing))}")
    unknown = cfg.keys() - COMPARATOR_ALLOWED_KEYS
    if unknown:
        f.add(f"comparator.json has unknown keys: {', '.join(sorted(unknown))}")
    if cfg.get("challenge_module") == cfg.get("solution_module"):
        f.add("comparator.json names the same module twice")
    permitted = cfg.get("permitted_axioms")
    if not isinstance(permitted, list) or not set(permitted) <= STANDARD_AXIOMS:
        f.add(f"comparator.json permitted_axioms is {permitted!r}; the registry "
              "accepts only the three classical axioms")
    names = cfg.get("theorem_names") or []
    if not names:
        f.add("comparator.json theorem_names is empty")

    for key in ("challenge_module", "solution_module"):
        module = cfg.get(key, "")
        if not isinstance(module, str) or not MODULE_RE.match(module):
            f.add(f"comparator.json {key} is {module!r}, which is not a dotted "
                  "Lean module name")
            continue
        expected = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not (expected.is_file() and not expected.is_symlink()):
            f.add(f"{key} {module} does not resolve to a regular file at "
                  f"{expected.relative_to(root)}")

    for name in names:
        short = str(name).split(".")[-1]
        sigs = {}
        for label, path in (("challenge", challenge(root)),
                            ("solution", solution(root))):
            if not re.search(rf"^theorem {re.escape(short)}\b",
                             path.read_text(encoding="utf-8"), re.MULTILINE):
                f.add(f"{path.relative_to(root)}: does not declare `{short}`, "
                      f"which comparator.json selects as {name}")
            else:
                sigs[label] = signature(path, short)
        if len(sigs) != 2:
            continue
        sc, ss = sigs["challenge"], sigs["solution"]
        if sc is None or ss is None:
            f.add(f"`{short}`: could not delimit the signature in both files "
                  "(no line ending in `:= by`), so it cannot be compared")
        elif sc != ss:
            for i, (x, y) in enumerate(zip(sc, ss)):
                if x != y:
                    f.add(f"`{short}`: the compared signature diverges at line "
                          f"{i + 1}: challenge {x!r} vs solution {y!r}")
                    break
            else:
                f.add(f"`{short}`: the compared signature is {len(sc)} lines in "
                      f"the challenge and {len(ss)} in the solution")


# --------------------------------------------------------------------------
# 5: the registry's intake rules, as far as the tree shows them
# --------------------------------------------------------------------------

def check_mechanical(root: Path, f: Findings) -> None:
    path = challenge(root)
    if path.is_file():
        data = path.read_bytes()
        lines = len(data.decode("utf-8", "replace").splitlines())
        if len(data) > MAX_CHALLENGE_BYTES:
            f.add(f"Palomar/Challenge.lean is {len(data)} bytes; the hard cap is "
                  f"{MAX_CHALLENGE_BYTES}")
        if lines > MAX_CHALLENGE_LINES:
            f.add(f"Palomar/Challenge.lean is {lines} lines; the hard cap is "
                  f"{MAX_CHALLENGE_LINES}")
        if len(data) > PREFERRED_CHALLENGE_BYTES or lines > PREFERRED_CHALLENGE_LINES:
            f.note(f"the challenge is {lines} lines / {len(data)} bytes, over the "
                   f"registry's preferred {PREFERRED_CHALLENGE_LINES}-line review "
                   "surface, so the mechanical report carries an advisory warning")

    licences = sorted(p for p in root.iterdir()
                      if p.is_file() and not p.is_symlink()
                      and LICENSE_FILE_RE.match(p.name))
    if len(licences) != 1:
        f.add("repository root must contain exactly one licence file; found "
              f"{[p.name for p in licences]}")
    else:
        size = licences[0].stat().st_size
        if size == 0 or size > MAX_LICENSE_BYTES:
            f.add(f"{licences[0].name} is {size} bytes; it must be nonempty and "
                  f"at most {MAX_LICENSE_BYTES}")

    toolchain_path = root / "lean-toolchain"
    if not toolchain_path.is_file():
        f.add("lean-toolchain is missing")
    else:
        toolchain = toolchain_path.read_text(encoding="utf-8").strip()
        m = TOOLCHAIN_RE.match(toolchain)
        if m is None:
            f.add(f"lean-toolchain is {toolchain!r}; the registry requires "
                  "`leanprover/lean4:vMAJOR.MINOR.PATCH[-rcN]`")
        elif (int(m["major"]), int(m["minor"]), int(m["patch"])) < MINIMUM_TOOLCHAIN:
            f.add(f"lean-toolchain {toolchain} is below the registry minimum "
                  f"v{'.'.join(map(str, MINIMUM_TOOLCHAIN))}")

    lakefiles = [p for p in (root / "lakefile.toml", root / "lakefile.lean")
                 if p.exists()]
    if len(lakefiles) != 1:
        f.add("project root must contain exactly one lakefile; found "
              f"{[p.name for p in lakefiles]}")
    elif lakefiles[0].stat().st_size > MAX_CONFIGURATION_BYTES:
        f.add(f"{lakefiles[0].name} exceeds the 1 MiB cap")

    if config_path(root).is_file() and \
            config_path(root).stat().st_size > MAX_CONFIGURATION_BYTES:
        f.add("comparator.json exceeds the 1 MiB cap")
    metadata = root / "formalization.yaml"
    if metadata.is_file() and metadata.stat().st_size > MAX_FORMALIZATION_BYTES:
        f.add("formalization.yaml exceeds the 256 KiB cap")

    manifest = root / "lake-manifest.json"
    if not manifest.is_file():
        f.add("lake-manifest.json is missing; the registry needs the exact "
              "dependency pins")
    else:
        for package in json.loads(
                manifest.read_text(encoding="utf-8")).get("packages", []):
            if package.get("type") != "git":
                continue
            name = package.get("name", "?")
            url = package.get("url") or ""
            if not GITHUB_URL_RE.match(url):
                f.add(f"dependency {name!r} has url {url!r}; the registry accepts "
                      "only a credential-free public https://github.com/owner/repo")
            rev = str(package.get("rev") or "")
            if not SHA_RE.fullmatch(rev):
                f.add(f"dependency {name!r} is pinned to {rev!r}, not a full "
                      "40-character lowercase commit SHA")

    # A symbolic link is refused only in these roles.  The registry does not
    # reject links elsewhere -- it excludes them from the size total -- so this
    # does not invent a rule the registry does not have.
    for role, p in (("comparator configuration", config_path(root)),
                    ("challenge source", challenge(root)),
                    ("solution source", solution(root)),
                    ("lake-manifest.json", manifest),
                    ("formalization.yaml", metadata),
                    ("lean-toolchain", toolchain_path)):
        if p.is_symlink():
            f.add(f"the {role} is a symbolic link; the registry requires a "
                  "regular file there")


def check_git_shapes(root: Path, f: Findings) -> None:
    """Build output, submodules and LFS, read the way the registry reads them.

    A `160000` index entry is a submodule gitlink, and `git check-attr filter`
    is what decides whether a path is LFS -- sniffing file contents would miss
    a path configured for LFS but not yet converted.
    """
    def git(*args: str, stdin: bytes | None = None) -> bytes | None:
        try:
            return subprocess.run(["git", *args], cwd=root, input=stdin,
                                  capture_output=True, check=True).stdout
        except (OSError, subprocess.CalledProcessError):
            return None

    stage = git("ls-files", "--stage", "-z")
    if stage is None:
        f.add("could not read the git index, so submodules could not be checked; "
              "that is the same as their being there")
        return
    for record in stage.decode("utf-8", "replace").split("\0"):
        if record and record.split(None, 1)[0] == "160000":
            f.add(f"{record.split(chr(9), 1)[-1]} is a Git submodule; the "
                  "registry rejects them because a fork does not preserve the "
                  "referenced repository")

    listing = git("ls-files", "-z")
    if listing is None:
        f.add("could not list tracked files, so the tree could not be checked")
        return
    for rel in listing.decode("utf-8", "replace").split("\0"):
        if not rel or rel.startswith(".lake/"):
            continue
        if Path(rel).suffix.lower() in COMPILED_ARTIFACT_SUFFIXES or \
                rel.endswith(COMPILED_ARTIFACT_NAME_SUFFIXES):
            f.add(f"{rel} is a compiled artifact and is tracked")

    attrs = git("check-attr", "--cached", "-z", "filter", "--stdin", stdin=listing)
    if attrs is None:
        f.add("could not read git attributes, so LFS could not be checked")
        return
    fields = attrs.decode("utf-8", "replace").split("\0")
    for i in range(0, max(0, len(fields) - 2), 3):
        path, attribute, value = fields[i : i + 3]
        if attribute == "filter" and value == "lfs":
            f.add(f"{path} is tracked with Git LFS; LFS objects are not "
                  "preservable and are rejected everywhere")


# --------------------------------------------------------------------------
# 6: the metadata contract
# --------------------------------------------------------------------------

def check_metadata(root: Path, f: Findings) -> None:
    try:
        import yaml  # noqa: PLC0415
    except ModuleNotFoundError:
        # Skipping is tolerable on a developer machine whose interpreter
        # happens to lack PyYAML, and is NOT tolerable in CI: a metadata check
        # that quietly does not run reads exactly like a metadata check that
        # passed.
        if os.environ.get("CI"):
            f.add("formalization.yaml could not be checked: PyYAML is not "
                  "importable, and a check that does not run must not look "
                  "like one that passed")
        else:
            print("palomar: formalization.yaml NOT CHECKED -- PyYAML is not "
                  "importable in this interpreter")
        return

    path = root / "formalization.yaml"
    if not path.is_file():
        f.add("formalization.yaml: missing")
        return
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        f.add("formalization.yaml must contain one top-level mapping")
        return

    project = data.get("project") or {}
    for key in ("name", "description"):
        if not (isinstance(project.get(key), str) and project[key].strip()):
            f.add(f"formalization.yaml: project.{key} must be a nonempty string")
    if isinstance(project.get("description"), str) and \
            len(project["description"]) > 10_000:
        f.add("formalization.yaml: project.description exceeds 10000 characters")
    for key in ("authors", "responsible_maintainers"):
        if not (isinstance(project.get(key), list) and project[key]):
            f.add(f"formalization.yaml: project.{key} must be a nonempty list")

    # The declared licence and the root licence file must identify the same
    # SPDX licence; the registry runs licensee over the file and compares.
    if project.get("license") != "Apache-2.0":
        f.add(f"formalization.yaml: project.license is {project.get('license')!r}; "
              "the root LICENSE is Apache-2.0 and the two must agree exactly")
    licence = root / "LICENSE"
    if not (licence.is_file()
            and "Apache License" in licence.read_text(encoding="utf-8")):
        f.add("LICENSE: not a readable Apache-2.0 licence file at the root")

    classification = data.get("classification") or {}
    arxiv = classification.get("arxiv")
    if not (isinstance(arxiv, list) and 1 <= len(arxiv) <= 2
            and len(set(arxiv)) == len(arxiv)):
        f.add(f"formalization.yaml: classification.arxiv is {arxiv!r}; the "
              "registry accepts one or two distinct official arXiv classes")
    msc = classification.get("msc2020")
    if not (isinstance(msc, list) and 1 <= len(msc) <= 8
            and len(set(msc)) == len(msc)):
        f.add(f"formalization.yaml: classification.msc2020 is {msc!r}; the "
              "registry accepts one to eight distinct MSC2020 codes")

    sources = data.get("sources")
    if not (isinstance(sources, list) and sources):
        f.add("formalization.yaml: sources must be a nonempty list")
        return
    origins = substantive = 0
    for i, src in enumerate(sources):
        if not isinstance(src, dict):
            f.add(f"formalization.yaml: sources[{i}] is not a mapping")
            continue
        if not (isinstance(src.get("title"), str) and src["title"].strip()):
            f.add(f"formalization.yaml: sources[{i}] has no nonempty title")
        rel = src.get("relationship")
        if rel not in RELATIONSHIPS:
            f.add(f"formalization.yaml: sources[{i}].relationship is {rel!r}; "
                  f"must be one of {sorted(RELATIONSHIPS)}")
        kind = src.get("type")
        if kind is not None and kind not in SOURCE_TYPES:
            f.add(f"formalization.yaml: sources[{i}].type is {kind!r}; must be "
                  f"one of {sorted(SOURCE_TYPES)} or absent")
        if kind == "original-proof":
            origins += 1
            if rel != "other":
                f.add(f"formalization.yaml: sources[{i}] declares the result "
                      f"origin but has relationship {rel!r}; an original-proof "
                      "entry must use `other`")
        if rel in SUBSTANTIVE:
            substantive += 1

    if origins and substantive:
        f.add(f"formalization.yaml: the source list declares an original result "
              f"({origins} original-proof entries) AND {substantive} substantive "
              "relationship(s); the two alternatives are exclusive")
    elif not origins and not substantive:
        f.add("formalization.yaml: the source list declares neither an "
              "original-proof entry nor any formalizes/adapts/"
              "independently-proves relationship, so it has no result origin")

    methods = (data.get("automation") or {}).get("methods")
    if not (isinstance(methods, list) and methods and all(
            isinstance(m, dict) and str(m.get("method", "")).strip()
            for m in methods)):
        f.add("formalization.yaml: automation.methods must be a nonempty list of "
              "mappings each carrying a nonempty `method`")
    status = (data.get("review") or {}).get("status")
    if not (isinstance(status, str) and status.strip()):
        f.add("formalization.yaml: review.status must be a nonempty string")


# --------------------------------------------------------------------------
# calibration
# --------------------------------------------------------------------------

CALIBRATION: tuple[tuple[str, str], ...] = (
    ("challenge over the line cap", "hard cap is 1000"),
    ("challenge with a project-local import", "may import Mathlib only"),
    ("shared block edited on one side", "shared block diverges"),
    ("signature edited on one side", "compared signature diverges"),
    ("second licence file at the root", "exactly one licence file"),
    ("toolchain below the minimum", "below the registry minimum"),
    ("dependency pinned to a branch", "not a full"),
    ("dependency hosted off github", "only a credential-free public"),
    ("comparator naming a missing module", "does not resolve to a regular file"),
    ("comparator permitting a fourth axiom", "only the three classical axioms"),
    ("tracked compiled artifact", "is a compiled artifact"),
    ("three arXiv classes", "one or two distinct official arXiv"),
    ("original result with a substantive source", "the two alternatives are exclusive"),
)

YAML_CALIBRATIONS = {
    "three arXiv classes",
    "original result with a substantive source",
}


def yaml_available() -> bool:
    try:
        import yaml  # noqa: F401, PLC0415
    except ModuleNotFoundError:
        return False
    return True


def plant(name: str, root: Path) -> None:
    """Introduce exactly one defect into a copy of the submission surface."""
    if name == "challenge over the line cap":
        path = challenge(root)
        path.write_text(path.read_text() + "\n" * 1200)
    elif name == "challenge with a project-local import":
        path = challenge(root)
        path.write_text("import GroupApproximation.Sofic.Sofic\n" + path.read_text())
    elif name == "shared block edited on one side":
        path = solution(root)
        path.write_text(path.read_text().replace(
            "structure FiniteCarrier where", "structure FiniteCarrier' where", 1))
    elif name == "signature edited on one side":
        path = solution(root)
        path.write_text(path.read_text().replace(
            "    IsSoficGroup E ∧ ¬", "    IsSoficGroup E ∧ True ∧ ¬", 1))
    elif name == "second licence file at the root":
        (root / "COPYING").write_text("copy\n")
    elif name == "toolchain below the minimum":
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.20.0\n")
    elif name == "dependency pinned to a branch":
        _edit_manifest(root, lambda p: p.update({"rev": "main"}))
    elif name == "dependency hosted off github":
        _edit_manifest(root, lambda p: p.update({"url": "https://gitlab.com/a/b"}))
    elif name == "comparator naming a missing module":
        _edit_config(root, lambda c: c.update({"solution_module": "Palomar.Nope"}))
    elif name == "comparator permitting a fourth axiom":
        _edit_config(root, lambda c: c["permitted_axioms"].append("sorryAx"))
    elif name == "tracked compiled artifact":
        (root / "Palomar" / "Challenge.olean").write_bytes(b"\0")
        subprocess.run(["git", "add", "Palomar/Challenge.olean"], cwd=root,
                       capture_output=True, check=False)
    elif name == "three arXiv classes":
        _edit_metadata(root, "  arxiv: [math.OA, math.GR]",
                       "  arxiv: [math.OA, math.GR, math.LO]")
    elif name == "original result with a substantive source":
        _edit_metadata(root, "    relationship: background",
                       "    relationship: formalizes", count=1)
    else:  # pragma: no cover
        raise AssertionError(f"no planter for {name!r}")


def _edit_manifest(root: Path, mutate) -> None:
    path = root / "lake-manifest.json"
    data = json.loads(path.read_text())
    for package in data.get("packages", []):
        if package.get("type") == "git":
            mutate(package)
            break
    path.write_text(json.dumps(data))


def _edit_config(root: Path, mutate) -> None:
    path = config_path(root)
    data = json.loads(path.read_text())
    mutate(data)
    path.write_text(json.dumps(data))


def _edit_metadata(root: Path, old: str, new: str, count: int = 1) -> None:
    path = root / "formalization.yaml"
    text = path.read_text()
    assert old in text, old
    path.write_text(text.replace(old, new, count))


def copy_surface(destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "Palomar").mkdir(exist_ok=True)
    for rel in ("Palomar/Challenge.lean", "PalomarSolution.lean",
                "Palomar/comparator.json", "LICENSE", "lean-toolchain",
                "lakefile.toml", "lake-manifest.json", "formalization.yaml"):
        (destination / rel).write_bytes((REPO / rel).read_bytes())
    subprocess.run(["git", "init", "-q"], cwd=destination, capture_output=True,
                   check=False)
    subprocess.run(["git", "add", "-A"], cwd=destination, capture_output=True,
                   check=False)


def self_test() -> int:
    failures = 0
    has_yaml = yaml_available()
    calibrated = 0
    skipped = 0
    with tempfile.TemporaryDirectory(prefix="palomar-clean-") as clean:
        root = Path(clean)
        copy_surface(root)
        f = Findings()
        check_files(root, f)
        check_mechanical(root, f)
        check_git_shapes(root, f)
        check_metadata(root, f)
        if f.rows:
            print("::error::[palomar] self-test: the CLEAN copy reported "
                  f"{len(f.rows)} finding(s); the gate is not calibrated")
            failures += 1
        else:
            print("self-test: clean copy has no findings (NOTE lines are advisory)")

    for name, marker in CALIBRATION:
        if name in YAML_CALIBRATIONS and not has_yaml:
            print(f"self-test: {name} -> SKIPPED (PyYAML is not importable)")
            skipped += 1
            continue
        calibrated += 1
        with tempfile.TemporaryDirectory(prefix="palomar-plant-") as directory:
            root = Path(directory)
            copy_surface(root)
            plant(name, root)
            f = Findings()
            check_files(root, f)
            check_mechanical(root, f)
            check_git_shapes(root, f)
            check_metadata(root, f)
            if any(marker in row for row in f.rows):
                print(f"self-test: {name} -> reported")
            else:
                print(f"::error::[palomar] self-test: {name} was NOT reported; "
                      f"expected a finding containing {marker!r}")
                failures += 1

    if failures:
        print(f"palomar self-test: {failures} calibration failure(s)")
        return 1
    print(f"palomar self-test: clean tree has no findings, {calibrated} planted "
          f"defects each reported, {skipped} YAML-dependent calibration(s) skipped")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    f = Findings()
    check_files(REPO, f)
    check_mechanical(REPO, f)
    check_git_shapes(REPO, f)
    check_metadata(REPO, f)
    if f.rows:
        print(f"palomar: {len(f.rows)} finding(s)")
        return 1
    print("palomar: shared block and compared signature identical, challenge "
          "imports Mathlib only, configuration resolves, tree and metadata meet "
          "the registry minimum")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
