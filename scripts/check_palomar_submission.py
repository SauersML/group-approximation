#!/usr/bin/env python3
"""Gate the Palomar submission surfaces.

A Palomar submission is exactly ONE Comparator configuration path, so a
repository offering two results is submitted twice, once per configuration
(PalomarRegistry's CONTRIBUTING rules; the kim-em/PalomarSubmission README).
This repository submits one, listed in `PALOMAR_CONFIGS`, and every check below
that is about a submission surface runs once per configuration with the
configuration path on its finding.  The challenge and solution paths are not
written down here: they are read out of each configuration's
`challenge_module` and `solution_module`, so a rename that updates the lakefile
and the JSON cannot leave this gate silently checking a file that no longer
participates in any submission.

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
   It must also publish, in `status.main_results`, every theorem every
   configuration submits, against that configuration: a submission surface the
   metadata never mentions describes a different repository from the one being
   submitted.  Checked only when PyYAML is importable; skipped, loudly, when it
   is not.

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
# `external_kernels` is the current spelling for replaying the export through
# an additional kernel; `enable_nanoda` is the backwards-compatible shorthand
# for the one that calls `nanoda_bin` (Comparator README, "Checking with
# Additional Kernels").  Neither appears in the committed configuration --
# `.github/workflows/palomar-comparator.yml` writes `enable_nanoda` into a
# throwaway copy from its own dispatch input, so the cost of the second replay
# stays a per-run decision -- but a config carrying either is legitimate and
# must not read as an unknown key here.
COMPARATOR_ALLOWED_KEYS = COMPARATOR_REQUIRED_KEYS | {
    "definition_names", "enable_nanoda", "external_kernels"}
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


# Every Comparator configuration this repository offers.  One configuration is
# one submission; the registry has no notion of a repository submitting two
# results at once, so the two entries below are two submissions of the same
# tree and each has to hold on its own.
PALOMAR_CONFIGS = (
    "Palomar/comparator-lix.json",  # the three ProblemLIX theorems
)

# Configurations whose SOLUTION is still a skeleton.
#
# `Palomar/LIXStrongSolution.lean` proves each of the three theorems its
# configuration selects from `GroupApproximation.NinetyNineProblems.ClimbedPowersOutside`,
# which follows from the one proposition the construction still owes,
# `NinetyNineProblems.LemmaTwoHoldsAtPowers` (`climbedPowersOutside_of_lemmaTwoHoldsAtPowers`),
# so its theorems carry a hypothesis the challenge's do not, under names ending `_of`.
# That is the honest state of the work and not a defect, so the pair is checked
# for everything that is meaningful now -- the configuration's shape, the
# challenge importing Mathlib alone, the size caps, the files existing, the
# shared block matching between its own two files -- and is excluded from
# exactly two rules:
#
#   * the challenge-versus-solution SIGNATURE comparison, which cannot hold
#     until the hypothesis is gone;
#   * the `formalization.yaml` requirement that every selected theorem be
#     published in `status.main_results`, because those rows carry
#     `sorry_count` and an axiom list and so assert a proved result.  Adding
#     them today would publish a claim that is false.
#
# An entry moves from here to `PALOMAR_CONFIGS` on the day its solution's
# theorems lose their hypotheses, and the metadata rows are added in the same
# change.  Nothing else about the gate changes.  A pending entry is NOT a
# weaker submission surface: it is not a submission surface at all, and the
# summary line says so.
PALOMAR_PENDING_CONFIGS = (
    "Palomar/comparator-lix-strong.json",  # the three ProblemLIXStrong theorems
)

# The files `copy_surface` copies and `--self-test` plants defects into.  The
# gate itself never names a challenge or a solution -- it derives both from a
# configuration -- so this list exists only so that a planter can corrupt a
# file without first parsing the configuration that names it.
SURFACE_FILES = (
    "Palomar/LIXChallenge.lean", "Palomar/LIXSolution.lean",
    "Palomar/comparator-lix.json",
    "Palomar/LIXStrongChallenge.lean", "Palomar/LIXStrongSolution.lean",
    "Palomar/comparator-lix-strong.json",
    "LICENSE", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "formalization.yaml",
)


class Pair:
    """One Comparator configuration together with the two files it names.

    `challenge` and `solution` are `None` when the configuration does not name
    a well-formed dotted module.  The finding for that is raised once, where
    the shape of the configuration is checked; every check that needs the file
    then does not run, rather than reporting the same defect a second time in
    a different vocabulary.
    """

    def __init__(self, root: Path, config_rel: str, cfg: dict,
                 pending: bool = False) -> None:
        self.root = root
        self.config_rel = config_rel
        self.config = root / config_rel
        self.cfg = cfg
        self.pending = pending
        self.challenge = self._module_path(cfg.get("challenge_module"))
        self.solution = self._module_path(cfg.get("solution_module"))

    def _module_path(self, module: object) -> Path | None:
        if not (isinstance(module, str) and MODULE_RE.match(module)):
            return None
        return self.root.joinpath(*module.split(".")).with_suffix(".lean")

    def rel(self, path: Path) -> str:
        return str(path.relative_to(self.root))

    def say(self, f: Findings, message: str) -> None:
        """Report `message` against this configuration.

        Every per-configuration finding carries the configuration path.  With
        two surfaces in one tree a bare `shared block diverges` does not say
        which submission is broken, and the reader would have to guess.
        """
        f.add(f"{self.config_rel}: {message}")


def load_pairs(root: Path, f: Findings) -> list[Pair]:
    """Parse every configuration, submittable and pending.

    A configuration that cannot be read is reported and dropped.  Everything
    downstream is a statement about what the configuration names, so there is
    nothing left to check once it is unreadable -- and saying so once beats
    reporting the same unreadable file under six different rules.

    A pending configuration is loaded on exactly the same terms as a
    submittable one; the difference lives in the two rules that consult
    `Pair.pending`, and nowhere else.  Loading it here rather than in a
    separate pass is what keeps a pending surface from rotting quietly: its
    files still have to exist, its challenge still has to import Mathlib alone,
    and its own two copies of the shared block still have to agree.
    """
    pairs: list[Pair] = []
    for rel, pending in ([(c, False) for c in PALOMAR_CONFIGS]
                         + [(c, True) for c in PALOMAR_PENDING_CONFIGS]):
        path = root / rel
        if not path.is_file():
            f.add(f"{rel}: missing")
            continue
        try:
            cfg = json.loads(path.read_text(encoding="utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            f.add(f"{rel}: is not valid UTF-8 JSON")
            continue
        if not isinstance(cfg, dict):
            f.add(f"{rel}: must contain one JSON object")
            continue
        pairs.append(Pair(root, rel, cfg, pending))
    return pairs


# --------------------------------------------------------------------------
# 1-4: the two files and the configuration, once per configuration
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
    """The compared theorem's signature: its `theorem` line through `:=`.

    Everything after that is the proof, which is supposed to differ.  Up to it,
    the two files must agree exactly: that text is the statement Comparator
    compares.

    The terminator is normalised: `:= by` is reported as `:=`.  A challenge
    always ends its statement with `:= by` and a `sorry`, while a solution may
    end it with a bare `:=` and give a term-mode proof -- two of the three LIX
    theorems in `Palomar/LIXSolution.lean` do.  That is a choice of proof MODE,
    not a difference in the statement; Comparator never sees it, because it
    compares elaborated `ConstantVal`s.  Keeping it would make this gate demand
    tactic mode on both sides, which is a rule the registry does not have and
    which would push a solution towards `:= by exact e` to satisfy a checker.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next((i for i, l in enumerate(lines)
                  if re.match(rf"^theorem {re.escape(short)}\b", l)), None)
    if start is None:
        return None
    for j in range(start, len(lines)):
        stripped = lines[j].rstrip()
        if stripped.endswith(":= by"):
            return lines[start:j] + [stripped[: -len(" by")]]
        if stripped.endswith(":="):
            return lines[start:j] + [stripped]
    return None


def check_files(root: Path, pairs: list[Pair], f: Findings) -> None:
    for pair in pairs:
        check_pair(root, pair, f)


def check_pair(root: Path, pair: Pair, f: Findings) -> None:
    """Everything that is about ONE submission surface.

    The configuration is read first, because the two files are whatever it
    names; if it names them badly there is nothing further to check on this
    surface, and the loop moves to the next configuration rather than
    reporting a missing file the reader would have to trace back.
    """
    cfg = pair.cfg
    missing = COMPARATOR_REQUIRED_KEYS - cfg.keys()
    if missing:
        pair.say(f, f"is missing {', '.join(sorted(missing))}")
    unknown = cfg.keys() - COMPARATOR_ALLOWED_KEYS
    if unknown:
        pair.say(f, f"has unknown keys: {', '.join(sorted(unknown))}")
    if cfg.get("challenge_module") == cfg.get("solution_module"):
        pair.say(f, "names the same module twice")
    permitted = cfg.get("permitted_axioms")
    if not isinstance(permitted, list) or not set(permitted) <= STANDARD_AXIOMS:
        pair.say(f, f"permitted_axioms is {permitted!r}; the registry accepts "
                    "only the three classical axioms")
    names = cfg.get("theorem_names") or []
    if not names:
        pair.say(f, "theorem_names is empty")

    # Shape checks for the optional keys.  They were allowed but unvalidated,
    # so `"enable_nanoda": "true"` -- a string, which is truthy in JSON-loading
    # code and false to Comparator's boolean field -- passed this gate while
    # silently turning the second kernel off.  Each check is guarded on the key
    # being present, so a configuration omitting them is unaffected.
    if "enable_nanoda" in cfg and not isinstance(cfg["enable_nanoda"], bool):
        pair.say(f, f"enable_nanoda is {cfg['enable_nanoda']!r}; Comparator "
                    "reads a JSON boolean, and a string here disables the "
                    "second kernel without failing anything")
    if "external_kernels" in cfg:
        ext = cfg["external_kernels"]
        if not isinstance(ext, dict) or not ext:
            pair.say(f, f"external_kernels is {ext!r}; it must be a nonempty "
                        "object mapping a kernel name to its argv array")
        else:
            for kernel, argv in ext.items():
                if not (isinstance(argv, list) and argv
                        and all(isinstance(a, str) for a in argv)):
                    pair.say(f, f"external_kernels[{kernel!r}] is {argv!r}; it "
                                "must be a nonempty array of strings")
    if "definition_names" in cfg:
        holes = cfg["definition_names"]
        if not (isinstance(holes, list)
                and all(isinstance(h, str) for h in holes)):
            pair.say(f, f"definition_names is {holes!r}; it must be an array "
                        "of declaration names")

    for key in ("challenge_module", "solution_module"):
        module = cfg.get(key, "")
        if not isinstance(module, str) or not MODULE_RE.match(module):
            pair.say(f, f"{key} is {module!r}, which is not a dotted Lean "
                        "module name")
            continue
        expected = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not (expected.is_file() and not expected.is_symlink()):
            pair.say(f, f"{key} {module} does not resolve to a regular file at "
                        f"{expected.relative_to(root)}")

    challenge, solution = pair.challenge, pair.solution
    if challenge is None or solution is None \
            or not challenge.is_file() or not solution.is_file():
        return

    a, b = shared_block(challenge), shared_block(solution)
    if a is None or b is None:
        pair.say(f, "shared-block markers not found in both files; the copy "
                    "cannot be checked, which is the same as it being wrong")
    elif a != b:
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                pair.say(f, f"shared block diverges at block line {i + 1}: "
                            f"{pair.rel(challenge)} {x!r} vs "
                            f"{pair.rel(solution)} {y!r}")
                break
        else:
            pair.say(f, f"shared block is {len(a)} lines in "
                        f"{pair.rel(challenge)} and {len(b)} in "
                        f"{pair.rel(solution)}")

    for n, line in enumerate(
            challenge.read_text(encoding="utf-8").splitlines(), 1):
        if IMPORT.match(line) and not ALLOWED_CHALLENGE_IMPORT.match(line):
            pair.say(f, f"{pair.rel(challenge)}:{n}: {line.strip()} -- the "
                        "challenge may import Mathlib only; a project-local "
                        "import fails mechanical verification at the registry")

    challenge_text = challenge.read_text(encoding="utf-8")
    solution_text = solution.read_text(encoding="utf-8")
    for name in names:
        short = str(name).split(".")[-1]
        sigs = {}
        if not re.search(rf"^theorem {re.escape(short)}\b", challenge_text,
                         re.MULTILINE):
            pair.say(f, f"{pair.rel(challenge)}: does not declare `{short}`, "
                        f"which the configuration selects as {name}")
        else:
            sigs["challenge"] = signature(challenge, short)

        if pair.pending:
            # The solution proves each selected statement from a proposition
            # the construction still owes, so it declares `<short>_of` and not
            # `<short>`; comparing signatures is meaningless until that
            # hypothesis is gone.  Requiring the `_of` name is what keeps a
            # pending surface from quietly losing a theorem: it is the one
            # thing about the pair that is still checkable, and a pending
            # entry with no check at all would certify nothing.
            #
            # The two patterns are disjoint: `_` is a word character, so `\b`
            # never matches between `<short>` and the `_of` that follows it, and
            # `^theorem <short>\b` therefore cannot be satisfied by a
            # declaration of `<short>_of`, nor the reverse.
            if not re.search(rf"^theorem {re.escape(short)}_of\b", solution_text,
                             re.MULTILINE):
                pair.say(f, f"{pair.rel(solution)}: does not declare "
                            f"`{short}_of`; while this configuration is "
                            "pending, every theorem it selects must appear in "
                            "the solution as the `_of` form carrying the "
                            "outstanding hypothesis")
            continue

        if not re.search(rf"^theorem {re.escape(short)}\b", solution_text,
                         re.MULTILINE):
            pair.say(f, f"{pair.rel(solution)}: does not declare `{short}`, "
                        f"which the configuration selects as {name}")
        else:
            sigs["solution"] = signature(solution, short)
        if len(sigs) != 2:
            continue
        sc, ss = sigs["challenge"], sigs["solution"]
        if sc is None or ss is None:
            pair.say(f, f"`{short}`: could not delimit the signature in both "
                        "files (no line ending in `:=` or `:= by`), so it "
                        "cannot be compared")
        elif sc != ss:
            for i, (x, y) in enumerate(zip(sc, ss)):
                if x != y:
                    pair.say(f, f"`{short}`: the compared signature diverges at "
                                f"line {i + 1}: challenge {x!r} vs "
                                f"solution {y!r}")
                    break
            else:
                pair.say(f, f"`{short}`: the compared signature is {len(sc)} "
                            f"lines in the challenge and {len(ss)} in the "
                            "solution")


# --------------------------------------------------------------------------
# 5: the registry's intake rules, as far as the tree shows them
# --------------------------------------------------------------------------

def check_mechanical(root: Path, pairs: list[Pair], f: Findings) -> None:
    # Per-configuration.  The caps are on the challenge and the configuration
    # of the submission being made, so each surface is measured on its own; a
    # second submission does not get to spend the first one's budget.
    for pair in pairs:
        if pair.challenge is not None and pair.challenge.is_file():
            data = pair.challenge.read_bytes()
            rel = pair.rel(pair.challenge)
            lines = len(data.decode("utf-8", "replace").splitlines())
            if len(data) > MAX_CHALLENGE_BYTES:
                pair.say(f, f"{rel} is {len(data)} bytes; the hard cap is "
                            f"{MAX_CHALLENGE_BYTES}")
            if lines > MAX_CHALLENGE_LINES:
                pair.say(f, f"{rel} is {lines} lines; the hard cap is "
                            f"{MAX_CHALLENGE_LINES}")
            if len(data) > PREFERRED_CHALLENGE_BYTES \
                    or lines > PREFERRED_CHALLENGE_LINES:
                f.note(f"{rel} is {lines} lines / {len(data)} bytes, over the "
                       f"registry's preferred {PREFERRED_CHALLENGE_LINES}-line "
                       "review surface, so the mechanical report carries an "
                       "advisory warning")
        if pair.config.is_file() \
                and pair.config.stat().st_size > MAX_CONFIGURATION_BYTES:
            pair.say(f, "exceeds the 1 MiB cap")

    # Repo-level from here down: one licence, one toolchain, one lakefile, one
    # dependency manifest.  These are properties of the tree, not of a
    # submission, so they are checked once however many configurations there
    # are -- reporting the same bad `lean-toolchain` twice would only make the
    # second finding look like a second defect.
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
    # does not invent a rule the registry does not have.  The three
    # tree-level roles are joined by each configuration's own three.
    roles: list[tuple[str, Path]] = [
        ("lake-manifest.json", manifest),
        ("formalization.yaml", metadata),
        ("lean-toolchain", toolchain_path),
    ]
    for pair in pairs:
        roles.append((f"{pair.config_rel} comparator configuration", pair.config))
        if pair.challenge is not None:
            roles.append((f"{pair.config_rel} challenge source", pair.challenge))
        if pair.solution is not None:
            roles.append((f"{pair.config_rel} solution source", pair.solution))
    for role, p in roles:
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

def check_metadata(root: Path, pairs: list[Pair], f: Findings) -> None:
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

    # Every theorem every configuration submits has to be published in
    # `status.main_results` against THAT configuration.  `formalization.yaml`
    # is one file per repository while a submission is one configuration, so
    # the correspondence between them is exactly the thing no single file
    # states; a second surface whose results were never added here submits a
    # metadata record describing a different repository.  This runs before the
    # `sources` block because that block returns early on a malformed list, and
    # an unrelated defect there must not silently take this check with it.
    published: dict[str, set[str]] = {}
    for i, row in enumerate((data.get("status") or {}).get("main_results") or []):
        if not isinstance(row, dict):
            f.add(f"formalization.yaml: status.main_results[{i}] is not a mapping")
            continue
        declaration, config = row.get("declaration"), row.get("comparator_config")
        if isinstance(declaration, str) and isinstance(config, str):
            published.setdefault(config, set()).add(declaration)
    for pair in pairs:
        # A pending configuration submits nothing, so the metadata must not
        # describe it.  A `status.main_results` row carries `sorry_count` and
        # an axiom list, which together assert a proved result; publishing one
        # for a theorem whose solution still takes a hypothesis would be a
        # false claim in the file the registry reads.  The rows are written in
        # the same change that moves the configuration to `PALOMAR_CONFIGS`.
        if pair.pending:
            f.note(f"{pair.config_rel} is pending, so its theorems are "
                   "deliberately absent from status.main_results")
            continue
        for name in pair.cfg.get("theorem_names") or []:
            if str(name) not in published.get(pair.config_rel, set()):
                f.add(f"formalization.yaml: {name} is not listed in "
                      f"status.main_results with comparator_config "
                      f"{pair.config_rel}; the metadata must publish every "
                      "theorem the configuration submits")

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

# The marker is a substring of the expected finding, and for a defect planted
# on one surface it names that surface: with two configurations in the tree, a
# marker like `shared block diverges` would be reported by whichever detector
# happened to fire, and a LIX planter satisfied by the non-MF detector is a
# calibration that certifies nothing.
CALIBRATION: tuple[tuple[str, str], ...] = (
    ("challenge over the line cap", "hard cap is 1000"),
    ("signature edited on one side", "compared signature diverges"),
    ("LIX challenge with a project-local import",
     "Palomar/LIXChallenge.lean:1:"),
    ("LIX shared block edited on one side",
     "Palomar/comparator-lix.json: shared block diverges"),
    ("second licence file at the root", "exactly one licence file"),
    ("toolchain below the minimum", "below the registry minimum"),
    ("dependency pinned to a branch", "not a full"),
    ("dependency hosted off github", "only a credential-free public"),
    ("comparator naming a missing module", "does not resolve to a regular file"),
    ("LIX comparator permitting a fourth axiom",
     "Palomar/comparator-lix.json: permitted_axioms"),
    # The pending third surface.  Its four calibrations are the four rules it
    # is still subject to; a pending entry whose planted defects went
    # unreported would be a configuration listed and checked by nothing.
    ("strong challenge with a project-local import",
     "Palomar/LIXStrongChallenge.lean:1:"),
    ("strong shared block edited on one side",
     "Palomar/comparator-lix-strong.json: shared block diverges"),
    ("strong solution missing an `_of` form",
     "does not declare `exists_simple_separable_order_six_witness_of`"),
    ("strong comparator permitting a fourth axiom",
     "Palomar/comparator-lix-strong.json: permitted_axioms"),
    ("tracked compiled artifact", "is a compiled artifact"),
    ("three arXiv classes", "one or two distinct official arXiv"),
    ("original result with a substantive source", "the two alternatives are exclusive"),
    ("LIX result dropped from the metadata", "is not listed in status.main_results"),
)

YAML_CALIBRATIONS = {
    "three arXiv classes",
    "original result with a substantive source",
    "LIX result dropped from the metadata",
}


def yaml_available() -> bool:
    try:
        import yaml  # noqa: F401, PLC0415
    except ModuleNotFoundError:
        return False
    return True


def plant(name: str, root: Path) -> None:
    """Introduce exactly one defect into a copy of the submission surface.

    Planters name files literally rather than resolving them through a
    configuration: a planter that read the configuration would stop planting
    the moment the configuration broke, which is the one case where the
    calibration matters most.
    """
    if name == "challenge over the line cap":
        path = root / "Palomar" / "LIXChallenge.lean"
        path.write_text(path.read_text() + "\n" * 1200)
    elif name == "signature edited on one side":
        path = root / "Palomar" / "LIXSolution.lean"
        path.write_text(path.read_text().replace(
            "IsSimpleRing A ∧ ¬ IsK1Injective A := by",
            "IsSimpleRing A ∧ True ∧ ¬ IsK1Injective A := by", 1))
    elif name == "LIX challenge with a project-local import":
        path = root / "Palomar" / "LIXChallenge.lean"
        path.write_text(
            "import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX\n"
            + path.read_text())
    elif name == "LIX shared block edited on one side":
        path = root / "Palomar" / "LIXSolution.lean"
        path.write_text(path.read_text().replace(
            "def cornerDiag (A : Type) [CStarAlgebra A] (n : ℕ) (a : A) :",
            "def cornerDiag' (A : Type) [CStarAlgebra A] (n : ℕ) (a : A) :", 1))
    elif name == "LIX comparator permitting a fourth axiom":
        _edit_config(root, "Palomar/comparator-lix.json",
                     lambda c: c["permitted_axioms"].append("sorryAx"))
    elif name == "strong challenge with a project-local import":
        path = root / "Palomar" / "LIXStrongChallenge.lean"
        path.write_text(
            "import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong\n"
            + path.read_text())
    elif name == "strong shared block edited on one side":
        path = root / "Palomar" / "LIXStrongSolution.lean"
        path.write_text(path.read_text().replace(
            "def cornerDiag (A : Type) [CStarAlgebra A] (n : ℕ) (a : A) :",
            "def cornerDiag' (A : Type) [CStarAlgebra A] (n : ℕ) (a : A) :", 1))
    elif name == "strong solution missing an `_of` form":
        path = root / "Palomar" / "LIXStrongSolution.lean"
        path.write_text(path.read_text().replace(
            "theorem exists_simple_separable_order_six_witness_of",
            "theorem exists_simple_separable_order_six_witness_renamed", 1))
    elif name == "strong comparator permitting a fourth axiom":
        _edit_config(root, "Palomar/comparator-lix-strong.json",
                     lambda c: c["permitted_axioms"].append("sorryAx"))
    elif name == "LIX result dropped from the metadata":
        _edit_metadata(root,
                       "    - declaration: ProblemLIX.not_all_simple_unital_k1Injective",
                       "    - declaration: ProblemLIX.renamed_and_not_republished")
    elif name == "second licence file at the root":
        (root / "COPYING").write_text("copy\n")
    elif name == "toolchain below the minimum":
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.20.0\n")
    elif name == "dependency pinned to a branch":
        _edit_manifest(root, lambda p: p.update({"rev": "main"}))
    elif name == "dependency hosted off github":
        _edit_manifest(root, lambda p: p.update({"url": "https://gitlab.com/a/b"}))
    elif name == "comparator naming a missing module":
        _edit_config(root, "Palomar/comparator-lix.json",
                     lambda c: c.update({"solution_module": "Palomar.Nope"}))
    elif name == "tracked compiled artifact":
        (root / "Palomar" / "LIXChallenge.olean").write_bytes(b"\0")
        subprocess.run(["git", "add", "Palomar/LIXChallenge.olean"], cwd=root,
                       capture_output=True, check=False)
    elif name == "three arXiv classes":
        _edit_metadata(root, "  arxiv: [math.OA, math.KT]",
                       "  arxiv: [math.OA, math.KT, math.LO]")
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


def _edit_config(root: Path, config_rel: str, mutate) -> None:
    path = root / config_rel
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
    for rel in SURFACE_FILES:
        (destination / rel).write_bytes((REPO / rel).read_bytes())
    subprocess.run(["git", "init", "-q"], cwd=destination, capture_output=True,
                   check=False)
    subprocess.run(["git", "add", "-A"], cwd=destination, capture_output=True,
                   check=False)


def run_all(root: Path, f: Findings) -> None:
    """Every check, in one place, so the gate and both self-test arms cannot
    drift apart: a calibration that exercises a check the real run does not
    perform, or the reverse, is worse than no calibration."""
    pairs = load_pairs(root, f)
    check_files(root, pairs, f)
    check_mechanical(root, pairs, f)
    check_git_shapes(root, f)
    check_metadata(root, pairs, f)


def self_test() -> int:
    failures = 0
    has_yaml = yaml_available()
    calibrated = 0
    skipped = 0
    with tempfile.TemporaryDirectory(prefix="palomar-clean-") as clean:
        root = Path(clean)
        copy_surface(root)
        f = Findings()
        run_all(root, f)
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
            run_all(root, f)
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
    run_all(REPO, f)
    if f.rows:
        print(f"palomar: {len(f.rows)} finding(s)")
        return 1
    print(f"palomar: {len(PALOMAR_CONFIGS)} submittable configuration(s) "
          f"({', '.join(PALOMAR_CONFIGS)}) each resolve, with shared block and "
          "every compared signature identical and the challenge importing "
          "Mathlib only; tree and metadata meet the registry minimum")
    if PALOMAR_PENDING_CONFIGS:
        print(f"palomar: {len(PALOMAR_PENDING_CONFIGS)} pending configuration(s) "
              f"({', '.join(PALOMAR_PENDING_CONFIGS)}) resolve, with shared "
              "block identical and the challenge importing Mathlib only; their "
              "signatures are NOT compared and their theorems are NOT published "
              "in formalization.yaml, because their solutions still carry a "
              "hypothesis -- they are not submission surfaces")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
