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

Both are checked here.

    REGRESSION  the import was present in the base revision, is absent in the
                head revision, and the module file still exists -- so the module
                is still in the repository but is no longer built
    DANGLING    the head revision imports a module whose file does not exist --
                lake reports "bad imports" and the whole build fails
    REMOVED     the import went away and so did the file (reported, not failed;
                deleting a module is a legitimate thing to do)

Usage:

    scripts/check_import_regression.py                  # origin/main~ -> working tree
    scripts/check_import_regression.py --base origin/main --head HEAD
    scripts/check_import_regression.py --root Other.lean

Exit status is 1 if any REGRESSION or DANGLING is found, else 0.
"""

import argparse
import subprocess
import sys
from pathlib import Path

IMPORT_PREFIX = "import "


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

    head_name = args.head or "working tree"
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

    if regressions or dangling:
        print()
        print(f"{len(regressions)} regression(s), {len(dangling)} dangling "
              f"import(s).")
        print("A dropped import does not fail CI -- it silently stops the "
              "module being built.")
        print("Append import lines rather than regenerating the block.")
        return 1

    print(f"no import regressions: {len(head)} module(s) imported at "
          f"{head_name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
