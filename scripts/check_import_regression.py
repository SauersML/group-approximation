#!/usr/bin/env python3
"""Catch root-import regressions between two revisions.

`scripts/check.py --list-orphans` reports the *state*: which modules are outside
the import closure right now.  That is not the dangerous condition.  The
dangerous one is the *transition* -- a module that was root-imported yesterday
and is not today -- because an unimported module and a broken one look identical
to CI, so a green module silently stops being checked and nobody is told.

This has happened twice: the root import block was regenerated, and committed,
green modules vanished from it.  A separate incident put the mirror-image defect
on main, an import of a module whose file was never committed, which makes lake
refuse to build anything at all.

A third transition does the same damage from the other side, and it is what
stalled certification on 2026-08-17: a module ADDED and never reached at all.
REGRESSION catches an import being taken away; NEW ORPHAN catches one that never
arrived.  The orphan set grew 0 -> 15 in a single day that way, and since
`check.py` fails on ANY orphan, each one blocked every certificate -- `verified`
could not advance however well the Lean compiled.

All are checked here.

    REGRESSION  the import was present in the base revision, is absent in the
                head revision, and the module file still exists -- so the module
                is still in the repository but is no longer built
    NEW ORPHAN  the module exists at the head revision, the root's import
                closure does not reach it, and it was not an orphan at the base
                revision -- so this change is what stopped it being compiled
    DANGLING    the head revision imports a module whose file does not exist --
                lake reports "bad imports" and the whole build fails
    REMOVED     the import went away and so did the file (reported, not failed;
                deleting a module is a legitimate thing to do)

Only the INCREASE in orphans fails.  Pre-existing orphans are listed and
tolerated, so a cleanup commit is never blocked by the orphans it has not got to
yet, and a push that wires some while adding none passes.

Usage:

    scripts/check_import_regression.py                  # origin/main~ -> working tree
    scripts/check_import_regression.py --base origin/main --head HEAD
    scripts/check_import_regression.py --root Other.lean

Exit status is 1 if any REGRESSION or DANGLING is found, else 0.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

IMPORT_PREFIX = "import "


def library_of(root):
    """The library directory: the root file's name without its extension.

    Derived rather than hardcoded so `--root Other.lean` keeps working.
    """
    return root[:-len(".lean")] if root.endswith(".lean") else root


def git(*args):
    """Run a git command and return stdout, or raise with git's own message."""
    result = subprocess.run(
        ["git"] + list(args), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        universal_newlines=True,
    )
    if result.returncode != 0:
        raise RuntimeError("git %s: %s" % (" ".join(args), result.stderr.strip()))
    return result.stdout


def read_revision(rev, path):
    """Read a file at a revision, or from the working tree when rev is None."""
    if rev is None:
        return Path(path).read_text()
    return git("show", f"{rev}:{path}")


def imported_modules(text):
    """The module names a root file imports, in the project's own namespace.

    Mathlib and other package imports are ignored: they are not ours to drop.
    """
    modules = set()
    for line in text.splitlines():
        line = line.strip()
        if line.startswith(IMPORT_PREFIX):
            name = line[len(IMPORT_PREFIX):].strip()
            if name.startswith("GroupApproximation."):
                modules.add(name)
    return modules


def module_path(module):
    return module.replace(".", "/") + ".lean"


def module_name(path):
    return path[:-len(".lean")].replace("/", ".")


def _tracked_modules(rev, lib):
    """Every library module at `rev` (or in the working tree when rev is None)."""
    if rev is None:
        return {
            module_name(str(p))
            for p in sorted(Path(lib).rglob("*.lean"))
        }
    listing = git("ls-tree", "-r", "--name-only", rev, "--", lib)
    return {
        module_name(line)
        for line in listing.splitlines()
        if line.endswith(".lean")
    }


def _imports_by_module(rev, lib):
    """module -> its library imports, in ONE git call rather than one per file.

    A per-file `git show` would be ~1400 subprocesses and turn a ten-second
    gate into a minutes-long one, which is the whole point of this gate.
    """
    if rev is None:
        result = {}
        for path in sorted(Path(lib).rglob("*.lean")):
            result[module_name(str(path))] = imported_modules(
                path.read_text(encoding="utf-8")
            )
        return result
    out = git("grep", "-n", f"^{IMPORT_PREFIX}{lib}", rev, "--", lib)
    pattern = re.compile(
        rf"^.*?:({lib}/\S+?\.lean):\d+:{IMPORT_PREFIX}({lib}\S*)\s*$"
    )
    result = {}
    for line in out.splitlines():
        matched = pattern.match(line)
        if matched:
            result.setdefault(module_name(matched.group(1)), set()).add(
                matched.group(2)
            )
    return result


def orphans_at(rev, root):
    """Modules present at `rev` that the root's import closure never reaches.

    An orphan is never compiled, so it is never checked: it rots silently while
    its badges keep pointing at it.  `scripts/check.py` reports this state and
    fails on it; this walks the same closure at an arbitrary revision so the
    *transition* can be compared.
    """
    lib = library_of(root)
    modules = _tracked_modules(rev, lib)
    if not modules:
        return set()
    imports = _imports_by_module(rev, lib)
    stack = [m for m in imported_modules(read_revision(rev, root)) if m in modules]
    seen = set()
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(i for i in imports.get(current, ()) if i in modules)
    return modules - seen


def exists_at(rev, path):
    if rev is None:
        return Path(path).exists()
    try:
        git("cat-file", "-e", f"{rev}:{path}")
        return True
    except RuntimeError:
        return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--base",
        default="origin/main~",
        help="revision to compare against (default: origin/main~)",
    )
    parser.add_argument(
        "--head",
        default=None,
        help="revision to check (default: the working tree)",
    )
    parser.add_argument(
        "--root",
        default="GroupApproximation.lean",
        help="root module file (default: GroupApproximation.lean)",
    )
    args = parser.parse_args()

    try:
        base_text = read_revision(args.base, args.root)
        head_text = read_revision(args.head, args.root)
    except (RuntimeError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    base = imported_modules(base_text)
    head = imported_modules(head_text)

    regressions = []
    removed = []
    for module in sorted(base - head):
        if exists_at(args.head, module_path(module)):
            regressions.append(module)
        else:
            removed.append(module)

    dangling = [
        module
        for module in sorted(head)
        if not exists_at(args.head, module_path(module))
    ]

    # The third transition, and the one that actually stalled certification on
    # 2026-08-17: a module ADDED without ever being reached.  REGRESSION catches
    # an import being taken away; this catches one that never arrived.  The
    # orphan set went 0 -> 15 in a day that way, and because `scripts/check.py`
    # fails on ANY orphan, every one of them blocked every certificate -- so
    # `verified` could not advance no matter how well the Lean compiled.
    #
    # Only the INCREASE fails.  A pre-existing orphan is reported and tolerated,
    # so the cleanup commits that remove them are never blocked by the ones
    # still outstanding, and a push that fixes some while adding none passes.
    try:
        base_orphans = orphans_at(args.base, args.root)
        head_orphans = orphans_at(args.head, args.root)
    except (RuntimeError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    new_orphans = sorted(head_orphans - base_orphans)
    surviving = sorted(head_orphans & base_orphans)

    head_name = args.head or "working tree"
    for module in new_orphans:
        print(f"NEW ORPHAN  {module}")
        print(f"            present at {head_name} but outside the import "
              f"closure, and it was not an orphan at {args.base}")
        print(f"            nothing compiles it, and it fails the Source scan "
              f"for every certificate")
    for module in regressions:
        print(f"REGRESSION  {module}")
        print(f"            imported at {args.base}, not at {head_name}, "
              f"file still present")
    for module in dangling:
        print(f"DANGLING    {module}")
        print(f"            imported at {head_name}, but "
              f"{module_path(module)} does not exist")
    for module in removed:
        print(f"REMOVED     {module}  (import and file both gone)")

    if surviving:
        print()
        print(f"{len(surviving)} pre-existing orphan(s), tolerated here so "
              f"cleanup is not blocked:")
        for module in surviving:
            print(f"            {module}")
        print("These still fail the Source scan, so no certificate passes "
              "until they are wired or deleted.")

    if regressions or dangling or new_orphans:
        print()
        print(f"{len(regressions)} regression(s), {len(dangling)} dangling "
              f"import(s), {len(new_orphans)} new orphan(s).")
        print("A dropped import does not fail CI -- it silently stops the "
              "module being built.")
        print("Append import lines rather than regenerating the block.")
        if new_orphans:
            print("Land a module and its root import in the SAME commit: an "
                  "unwired module is compiled by nothing, and wiring it later "
                  "elaborates it for the first time inside a certificate run, "
                  "where a fatal linter costs hours instead of seconds.")
        return 1

    print(f"no import regressions: {len(head)} module(s) imported at "
          f"{head_name}, no new orphans")
    return 0


if __name__ == "__main__":
    sys.exit(main())
