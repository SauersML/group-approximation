#!/usr/bin/env python3
"""Advance ``verified`` without weakening its proof boundary.

There are two legitimate sources of a certified base revision:

* the commit whose complete Prover job has just succeeded; or
* the current remote ``verified`` tip itself.

From that base, this script may include later publication-only commits.  It
does so only when every verification-relevant Git tree entry -- blob (or
submodule) object id *and* mode -- is identical at *every* intervening commit.
An unsafe edit followed by a revert therefore cannot smuggle the unsafe
intermediate commit onto ``verified``.  New or unknown paths are
verification-relevant by default.  The deliberately small publication-only
surface is defined once below and shared by both promotion workflows.

The remote update is an ordinary non-force push.  An ancestry check precedes
it, and a rejected push is accepted as a benign race only when the new remote
tip already contains the candidate.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import Callable, Mapping, Sequence


# These files can change the human-facing repository without changing a proof
# or its theorem/reference contracts.  Everything not explicitly covered here
# is relevant and therefore blocks lightweight promotion.
PUBLICATION_ONLY_FILES = frozenset(
    {
        ".gitignore",
        "CITATION.cff",
        "LICENSE",
        "README.md",
        "docbuild/lake-manifest.json",
        "docbuild/lakefile.toml",
        "docbuild/lean-toolchain",
        "non_mf_groups_exist.pdf",
        "references/README.md",
    }
)

# These are under the otherwise publication-only notes/ directory, but they are
# direct inputs to source/reference/signature gates.  Keeping the exception
# list beside the allowlist makes a broad notes/ rule impossible to overlook.
VERIFICATION_DOC_FILES = frozenset(
    {
        "metadata/CLAIM_DECLS.txt",
        "metadata/CLAIM_MAP.md",
        "metadata/CLAIM_SIGNATURES.md",
        "metadata/NON_MF_CLAIM_DECLS.txt",
        "metadata/NON_MF_CLAIM_SIGNATURES.md",
        "metadata/NON_MF_NUMBERED_CLAIMS.json",
    }
)


def is_publication_only(path: str) -> bool:
    """Return whether *path* is in the narrow non-verification surface."""
    if path in PUBLICATION_ONLY_FILES:
        return True
    # A future Lean file under notes/ or metadata/ is proof-relevant even if
    # it has a .md sibling.  Unknown extensions also fail closed.
    # metadata/ holds the machine-consumed audit artifacts that used to live
    # under notes/ (notes/ keeps prose notes plus compat symlinks); the same
    # md-only publication rule applies to both.
    return (
        (path.startswith("notes/") or path.startswith("metadata/"))
        and PurePosixPath(path).suffix == ".md"
        and path not in VERIFICATION_DOC_FILES
    )


TreeEntry = tuple[str, str, str]  # mode, Git object type, object id


@dataclass(frozen=True)
class TreeComparison:
    publication_changes: tuple[str, ...]
    verification_changes: tuple[str, ...]

    @property
    def equivalent(self) -> bool:
        return not self.verification_changes


def compare_tree_maps(
    base: Mapping[str, TreeEntry], target: Mapping[str, TreeEntry]
) -> TreeComparison:
    changed = sorted(
        path for path in base.keys() | target.keys() if base.get(path) != target.get(path)
    )
    publication = tuple(path for path in changed if is_publication_only(path))
    verification = tuple(path for path in changed if not is_publication_only(path))
    return TreeComparison(publication, verification)


def run_git(*args: str, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(
        ["git", *args],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and result.returncode != 0:
        command = "git " + " ".join(args)
        stderr = result.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"{command} failed ({result.returncode}): {stderr}")
    return result


def resolve(ref: str) -> str:
    return run_git("rev-parse", "--verify", f"{ref}^{{commit}}").stdout.decode().strip()


def is_ancestor(ancestor: str, descendant: str) -> bool:
    result = run_git("merge-base", "--is-ancestor", ancestor, descendant, check=False)
    if result.returncode == 0:
        return True
    if result.returncode == 1:
        return False
    stderr = result.stderr.decode("utf-8", errors="replace").strip()
    raise RuntimeError(
        f"git merge-base --is-ancestor failed ({result.returncode}): {stderr}"
    )


def read_tree(revision: str) -> dict[str, TreeEntry]:
    raw = run_git("ls-tree", "-rz", "--full-tree", revision).stdout
    tree: dict[str, TreeEntry] = {}
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, object_type, object_id = metadata.decode("ascii").split(" ")
        path = raw_path.decode("utf-8", errors="strict")
        tree[path] = (mode, object_type, object_id)
    return tree


def compare_tree_sequence(
    base: Mapping[str, TreeEntry], descendants: Sequence[Mapping[str, TreeEntry]]
) -> TreeComparison:
    """Compare every descendant tree with the certified base tree."""
    publication: set[str] = set()
    verification: set[str] = set()
    for descendant in descendants:
        comparison = compare_tree_maps(base, descendant)
        publication.update(comparison.publication_changes)
        verification.update(comparison.verification_changes)
    return TreeComparison(tuple(sorted(publication)), tuple(sorted(verification)))


def compare_revisions(base: str, target: str) -> TreeComparison:
    """Compare the whole ancestry range, not merely its two endpoint trees."""
    revisions = run_git("rev-list", "--reverse", f"{base}..{target}").stdout
    descendants = [read_tree(revision.decode("ascii"))
                   for revision in revisions.splitlines()]
    return compare_tree_sequence(read_tree(base), descendants)


def choose_certified_base(
    certified: str,
    current_verified: str,
    main: str,
    ancestor: Callable[[str, str], bool] = is_ancestor,
) -> str:
    """Choose the newest known-certified ancestor, rejecting divergence."""
    if not ancestor(certified, main):
        raise RuntimeError(
            f"certified commit {certified} is not an ancestor of main {main}"
        )
    if not ancestor(current_verified, main):
        raise RuntimeError(
            f"verified tip {current_verified} is not an ancestor of main {main}"
        )
    if ancestor(current_verified, certified):
        return certified
    if ancestor(certified, current_verified):
        return current_verified
    raise RuntimeError(
        f"verified tip {current_verified} diverged from certified commit {certified}"
    )


def _report(comparison: TreeComparison, *, limit: int = 30) -> None:
    if comparison.publication_changes:
        print(
            "Publication-only changes: "
            + ", ".join(comparison.publication_changes[:limit])
        )
        if len(comparison.publication_changes) > limit:
            print(
                f"  ... and {len(comparison.publication_changes) - limit} more"
            )
    if comparison.verification_changes:
        print("Verification-relevant changes block lightweight promotion:")
        for path in comparison.verification_changes[:limit]:
            print(f"  {path}")
        if len(comparison.verification_changes) > limit:
            print(
                f"  ... and {len(comparison.verification_changes) - limit} more"
            )


def compare_command(base_ref: str, target_ref: str) -> int:
    base = resolve(base_ref)
    target = resolve(target_ref)
    if not is_ancestor(base, target):
        raise RuntimeError(f"base {base} is not an ancestor of target {target}")
    comparison = compare_revisions(base, target)
    _report(comparison)
    if comparison.equivalent:
        print(f"Verification-relevant trees are byte-identical: {base} -> {target}")
        return 0
    return 1


def advance_command(
    *, certified_ref: str, main_ref: str, verified_ref: str, remote: str
) -> int:
    certified = resolve(certified_ref)
    main = resolve(main_ref)
    current = resolve(verified_ref)
    base = choose_certified_base(certified, current, main)
    comparison = compare_revisions(base, main)
    _report(comparison)

    candidate = main if comparison.equivalent else base
    if candidate == current:
        if comparison.equivalent:
            print(f"verified already points at the newest safe commit {current}")
        else:
            print(
                f"verified remains at {current}; a full Prover success is required "
                "for the listed paths"
            )
        return 0
    if is_ancestor(candidate, current):
        print(f"verified already contains candidate {candidate} at {current}")
        return 0
    if not is_ancestor(current, candidate):
        raise RuntimeError(
            f"refusing non-fast-forward update from {current} to {candidate}"
        )

    push = run_git(
        "push", remote, f"{candidate}:refs/heads/verified", check=False
    )
    if push.returncode == 0:
        print(f"verified fast-forwarded from {current} to {candidate}")
        return 0

    # Another promotion job may have won the race.  Refresh only the tracking
    # ref, then accept the rejection iff that remote tip already contains our
    # candidate.  No force push is ever attempted.
    run_git(
        "fetch",
        "--no-tags",
        remote,
        "+refs/heads/verified:refs/remotes/origin/verified",
    )
    concurrent = resolve("refs/remotes/origin/verified")
    if is_ancestor(candidate, concurrent):
        print(f"verified advanced concurrently to {concurrent}")
        return 0
    stderr = push.stderr.decode("utf-8", errors="replace").strip()
    raise RuntimeError(
        f"verified push was rejected and remote {concurrent} does not contain "
        f"candidate {candidate}: {stderr}"
    )


def self_test() -> int:
    blob_a: TreeEntry = ("100644", "blob", "a" * 40)
    blob_b: TreeEntry = ("100644", "blob", "b" * 40)
    executable_a: TreeEntry = ("100755", "blob", "a" * 40)

    assert is_publication_only("README.md")
    assert is_publication_only("notes/NOTEPAD.md")
    assert not is_publication_only("metadata/CLAIM_SIGNATURES.md")
    assert not is_publication_only("references/counterexample.tex")
    assert not is_publication_only("notes/new_proof.lean")
    assert not is_publication_only("scripts/advance_verified_branch.py")
    assert not is_publication_only(".github/workflows/verified-promote.yml")
    assert not is_publication_only(".github/workflows/verified-fast-forward.yml")
    assert not is_publication_only("unknown/new-file.txt")

    docs_only = compare_tree_maps(
        {"GroupApproximation.lean": blob_a, "README.md": blob_a},
        {"GroupApproximation.lean": blob_a, "README.md": blob_b},
    )
    assert docs_only.equivalent
    assert docs_only.publication_changes == ("README.md",)

    source_change = compare_tree_maps(
        {"GroupApproximation.lean": blob_a},
        {"GroupApproximation.lean": blob_b},
    )
    assert not source_change.equivalent
    assert source_change.verification_changes == ("GroupApproximation.lean",)

    mode_change = compare_tree_maps(
        {"scripts/check.py": blob_a}, {"scripts/check.py": executable_a}
    )
    assert not mode_change.equivalent

    # Endpoint equality is insufficient: every commit reachable from verified
    # is part of the branch.  A proof edit followed by a revert must block the
    # lightweight path even though the final proof tree matches the base.
    reverted_proof_edit = compare_tree_sequence(
        {"GroupApproximation.lean": blob_a},
        [
            {"GroupApproximation.lean": blob_b},
            {"GroupApproximation.lean": blob_a},
        ],
    )
    assert not reverted_proof_edit.equivalent

    ancestry = {
        ("old", "old"),
        ("old", "green"),
        ("old", "main"),
        ("green", "green"),
        ("green", "main"),
        ("main", "main"),
    }
    fake_ancestor = lambda left, right: (left, right) in ancestry
    assert choose_certified_base("green", "old", "main", fake_ancestor) == "green"
    assert choose_certified_base("old", "green", "main", fake_ancestor) == "green"

    print("self-test: verified-branch classifier and ancestry planner passed")
    return 0


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    compare = subparsers.add_parser(
        "compare", help="compare two revisions' verification-relevant trees"
    )
    compare.add_argument("base_ref")
    compare.add_argument("target_ref")

    advance = subparsers.add_parser(
        "advance", help="safely advance refs/heads/verified"
    )
    advance.add_argument("--certified-ref", required=True)
    advance.add_argument("--main-ref", required=True)
    advance.add_argument("--verified-ref", required=True)
    advance.add_argument("--remote", default="origin")

    subparsers.add_parser("self-test", help="calibrate the classifier")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "self-test":
            return self_test()
        if args.command == "compare":
            return compare_command(args.base_ref, args.target_ref)
        if args.command == "advance":
            return advance_command(
                certified_ref=args.certified_ref,
                main_ref=args.main_ref,
                verified_ref=args.verified_ref,
                remote=args.remote,
            )
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    raise AssertionError(f"unhandled command {args.command}")


if __name__ == "__main__":
    raise SystemExit(main())
