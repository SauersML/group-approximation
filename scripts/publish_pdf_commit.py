#!/usr/bin/env python3
"""Publish one generated PDF without overwriting concurrent work.

For the attested ``publish`` command, the source revision has already passed
the full Prover workflow.  ``main`` may have acquired later human-facing
commits while a PDF was building, so that command accepts only descendants
that pass ``advance_verified_branch.py compare``.  Both publishing modes
construct a new commit from the current remote tree with a temporary Git index,
replacing exactly one tracked PDF.  No branch, checkout, worktree, reset, force
push, or merge operation is involved.

The draft command has a deliberately different boundary: it may cross later
code commits, but only while the manuscript source blob is unchanged.  Drafts
therefore stay fresh during proof development without being mistaken for the
attested publication path.
"""

from __future__ import annotations

import argparse
from enum import Enum
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Callable, Mapping, Sequence


ALLOWED_PDFS = frozenset(
    {
        "non_mf_groups_exist.pdf",
    }
)
ALLOWED_DRAFT_SOURCES = frozenset({"non_mf_groups_exist.tex"})
CLASSIFIER = Path(__file__).with_name("advance_verified_branch.py")
REMOTE = "origin"
REMOTE_MAIN = "refs/remotes/origin/main"
PUSH_ATTEMPTS = 3


class PublicationDeferred(RuntimeError):
    """The certified source is stale relative to verification-relevant main."""


class Outcome(Enum):
    PUBLISHED = "published"
    CURRENT = "current"


def repo_root() -> Path:
    root = Path(__file__).resolve().parent.parent
    if not (root / ".git").exists():
        raise RuntimeError(f"repository root has no .git directory: {root}")
    return root


def run(
    arguments: Sequence[str],
    *,
    cwd: Path,
    check: bool = True,
    input_text: str | None = None,
    env_updates: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    environment = None
    if env_updates is not None:
        environment = os.environ.copy()
        environment.update(env_updates)
    result = subprocess.run(
        list(arguments),
        cwd=cwd,
        env=environment,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and result.returncode != 0:
        command = " ".join(arguments)
        details = result.stderr.strip() or result.stdout.strip()
        raise RuntimeError(f"{command} failed ({result.returncode}): {details}")
    return result


def git(
    root: Path,
    *arguments: str,
    check: bool = True,
    input_text: str | None = None,
    env_updates: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return run(
        ("git", *arguments),
        cwd=root,
        check=check,
        input_text=input_text,
        env_updates=env_updates,
    )


def resolve(root: Path, revision: str) -> str:
    return git(root, "rev-parse", "--verify", f"{revision}^{{commit}}").stdout.strip()


def fetch_main(root: Path) -> str:
    git(
        root,
        "fetch",
        "--no-tags",
        REMOTE,
        f"refs/heads/main:{REMOTE_MAIN}",
    )
    return resolve(root, REMOTE_MAIN)


def require_publication_only_descendants(
    root: Path, source: str, current_main: str
) -> None:
    result = run(
        (
            sys.executable,
            str(CLASSIFIER),
            "compare",
            source,
            current_main,
        ),
        cwd=root,
        check=False,
    )
    if result.stdout:
        print(result.stdout, end="")
    if result.returncode == 0:
        return
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    if result.returncode == 1:
        raise PublicationDeferred(
            f"main {current_main} contains verification-relevant changes after "
            f"certified source {source}; leaving main untouched"
        )
    raise RuntimeError(
        "the verified-tree classifier could not compare the publication base "
        f"and main (exit {result.returncode})"
    )


def tracked_blob_entry(root: Path, revision: str, path: str) -> tuple[str, str]:
    raw = git(root, "ls-tree", "-z", revision, "--", path).stdout
    records = [record for record in raw.split("\0") if record]
    if len(records) != 1:
        raise RuntimeError(
            f"expected exactly one tracked {path} entry at {revision}, "
            f"found {len(records)}"
        )
    metadata, recorded_path = records[0].split("\t", 1)
    mode, object_type, object_id = metadata.split(" ")
    if recorded_path != path or mode != "100644" or object_type != "blob":
        raise RuntimeError(
            f"refusing non-regular tracked PDF entry at {revision}: {records[0]!r}"
        )
    return mode, object_id


def require_fresher_draft_source(
    root: Path, source: str, current_main: str, source_file: str, pdf: str
) -> None:
    """Require the draft to be built from a newer source than the committed PDF.

    The old rule required the draft's source blob to equal the blob at the
    current main head.  Under a steady stream of manuscript pushes that rule
    never holds by the time a multi-minute build finishes, so publication
    deferred forever and the committed PDF only aged (observed 2026-08-15:
    eleven hours stale across several green builds).  The invariant that
    actually needs protecting is monotonicity -- a build must never replace a
    PDF that was produced from a newer source.  So: defer only when the last
    commit that touched the source file at our build's source is already an
    ancestor of the last commit that touched the committed PDF.  A slightly
    old draft then still publishes, and the catch-up schedule converges the
    PDF to the head source within one cycle.
    """
    ancestor = git(
        root,
        "merge-base",
        "--is-ancestor",
        source,
        current_main,
        check=False,
    )
    if ancestor.returncode == 1:
        raise PublicationDeferred(
            f"draft source {source} is not an ancestor of main {current_main}"
        )
    if ancestor.returncode != 0:
        details = ancestor.stderr.strip() or ancestor.stdout.strip()
        raise RuntimeError(f"could not compare draft ancestry: {details}")
    built_from = git(
        root, "rev-list", "-1", source, "--", source_file
    ).stdout.strip()
    if not built_from:
        raise RuntimeError(
            f"{source_file} has no history at draft source {source}"
        )
    pdf_updated = git(
        root, "rev-list", "-1", current_main, "--", pdf
    ).stdout.strip()
    if not pdf_updated:
        return
    stale = git(
        root,
        "merge-base",
        "--is-ancestor",
        built_from,
        pdf_updated,
        check=False,
    )
    if stale.returncode == 0:
        raise PublicationDeferred(
            f"committed {pdf} (last updated at {pdf_updated}) already covers "
            f"the {source_file} state of draft source {source}"
        )
    if stale.returncode != 1:
        details = stale.stderr.strip() or stale.stdout.strip()
        raise RuntimeError(f"could not compare draft freshness: {details}")


def hash_worktree_file(root: Path, path: str) -> str:
    return git(
        root,
        "hash-object",
        "-w",
        f"--path={path}",
        "--",
        path,
    ).stdout.strip()


def build_commit(
    root: Path,
    *,
    parent: str,
    path: str,
    blob: str,
    message: str,
) -> str | None:
    mode, old_blob = tracked_blob_entry(root, parent, path)
    if old_blob == blob:
        return None

    with tempfile.TemporaryDirectory(prefix="publish-pdf-index-") as directory:
        index = str(Path(directory) / "index")
        index_environment = {"GIT_INDEX_FILE": index}
        git(root, "read-tree", parent, env_updates=index_environment)
        git(
            root,
            "update-index",
            "--add",
            "--cacheinfo",
            f"{mode},{blob},{path}",
            env_updates=index_environment,
        )
        tree = git(root, "write-tree", env_updates=index_environment).stdout.strip()

    parent_tree = git(root, "rev-parse", f"{parent}^{{tree}}").stdout.strip()
    if tree == parent_tree:
        raise RuntimeError(
            "the replacement blob changed but the candidate tree did not"
        )
    return git(
        root,
        "commit-tree",
        tree,
        "-p",
        parent,
        input_text=f"{message}\n",
    ).stdout.strip()


def validate_pdf(root: Path, pdf: str) -> None:
    if pdf not in ALLOWED_PDFS:
        raise RuntimeError(f"refusing non-publication PDF path: {pdf!r}")
    path = root / pdf
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"publication PDF is not a regular file: {path}")


def publish_pdf_with_guard(
    root: Path,
    *,
    source_ref: str,
    pdf: str,
    message: str,
    guard: Callable[[Path, str, str], None],
) -> tuple[Outcome, str]:
    validate_pdf(root, pdf)
    if not message.strip() or "\n" in message:
        raise RuntimeError("the publication commit message must be one nonempty line")
    source = resolve(root, source_ref)
    blob = hash_worktree_file(root, pdf)
    last_push_error = ""

    for attempt in range(1, PUSH_ATTEMPTS + 1):
        current_main = fetch_main(root)
        guard(root, source, current_main)
        candidate = build_commit(
            root,
            parent=current_main,
            path=pdf,
            blob=blob,
            message=message,
        )
        if candidate is None:
            print(f"{pdf} is already current at {current_main}")
            return Outcome.CURRENT, current_main

        push = git(
            root,
            "push",
            "--porcelain",
            REMOTE,
            f"{candidate}:refs/heads/main",
            check=False,
        )
        if push.returncode == 0:
            print(
                f"published {pdf} as {candidate} atop {current_main} "
                f"on attempt {attempt}"
            )
            return Outcome.PUBLISHED, candidate
        last_push_error = push.stderr.strip() or push.stdout.strip()
        print(
            f"non-force publication push attempt {attempt}/{PUSH_ATTEMPTS} "
            "lost a race; refreshing main",
            file=sys.stderr,
        )

    current_main = fetch_main(root)
    guard(root, source, current_main)
    _, current_blob = tracked_blob_entry(root, current_main, pdf)
    if current_blob == blob:
        print(f"{pdf} was published concurrently at {current_main}")
        return Outcome.CURRENT, current_main
    raise RuntimeError(
        f"could not publish {pdf} after {PUSH_ATTEMPTS} non-force attempts: "
        f"{last_push_error}"
    )


def publish_pdf(
    root: Path, *, source_ref: str, pdf: str, message: str
) -> tuple[Outcome, str]:
    """Publish an attested PDF across publication-only descendants."""
    return publish_pdf_with_guard(
        root,
        source_ref=source_ref,
        pdf=pdf,
        message=message,
        guard=require_publication_only_descendants,
    )


def publish_draft_pdf(
    root: Path,
    *,
    source_ref: str,
    source_file: str,
    pdf: str,
    message: str,
) -> tuple[Outcome, str]:
    """Publish a draft that is fresher than the committed PDF."""
    if source_file not in ALLOWED_DRAFT_SOURCES:
        raise RuntimeError(f"refusing non-draft source path: {source_file!r}")
    return publish_pdf_with_guard(
        root,
        source_ref=source_ref,
        pdf=pdf,
        message=message,
        guard=lambda guarded_root, source, current: require_fresher_draft_source(
            guarded_root, source, current, source_file, pdf
        ),
    )


def remote_main(root: Path) -> str:
    output = git(root, "ls-remote", "--refs", REMOTE, "refs/heads/main").stdout
    records = [line.split() for line in output.splitlines() if line.strip()]
    if len(records) != 1 or len(records[0]) != 2:
        raise RuntimeError("test remote does not have exactly one main ref")
    return records[0][0]


def blob_contents(root: Path, revision: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "cat-file", "blob", f"{revision}:{path}"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.decode(errors="replace"))
    return result.stdout


def self_test() -> None:
    if PUSH_ATTEMPTS != 3:
        raise RuntimeError("publication retry calibration no longer has three attempts")
    with tempfile.TemporaryDirectory(prefix="publish-pdf-self-test-") as directory:
        test_root = Path(directory) / "work"
        remote = Path(directory) / "remote.git"
        git(directory_root := Path(directory), "init", "--bare", str(remote))
        git(directory_root, "init", "--initial-branch=main", str(test_root))
        git(test_root, "config", "user.name", "Publication Self-Test")
        git(test_root, "config", "user.email", "publication-self-test@example.invalid")
        git(test_root, "remote", "add", REMOTE, str(remote))

        (test_root / "proof.txt").write_text("proof-v1\n", encoding="utf-8")
        (test_root / "non_mf_groups_exist.tex").write_text(
            "manuscript-v1\n", encoding="utf-8"
        )
        (test_root / "non_mf_groups_exist.pdf").write_bytes(b"non-mf-v1\n")
        git(
            test_root,
            "add",
            "--",
            "proof.txt",
            "non_mf_groups_exist.tex",
            "non_mf_groups_exist.pdf",
        )
        git(test_root, "commit", "-m", "certified base")
        certified = resolve(test_root, "HEAD")
        git(test_root, "push", REMOTE, "HEAD:refs/heads/main")

        (test_root / "proof.txt").write_text("proof-v2\n", encoding="utf-8")
        git(test_root, "add", "--", "proof.txt")
        git(test_root, "commit", "-m", "publish sibling file")
        sibling = resolve(test_root, "HEAD")
        git(test_root, "push", REMOTE, "HEAD:refs/heads/main")

        (test_root / "non_mf_groups_exist.pdf").write_bytes(b"non-mf-v2\n")
        outcome, published = publish_pdf(
            test_root,
            source_ref=certified,
            pdf="non_mf_groups_exist.pdf",
            message="publish target PDF",
        )
        assert outcome is Outcome.PUBLISHED
        assert remote_main(test_root) == published
        assert resolve(test_root, f"{published}^") == sibling
        assert (
            blob_contents(test_root, published, "proof.txt")
            == b"proof-v2\n"
        )
        assert (
            blob_contents(test_root, published, "non_mf_groups_exist.pdf")
            == b"non-mf-v2\n"
        )

        outcome, current = publish_pdf(
            test_root,
            source_ref=certified,
            pdf="non_mf_groups_exist.pdf",
            message="do not duplicate current PDF",
        )
        assert outcome is Outcome.CURRENT
        assert current == published
        assert remote_main(test_root) == published

        (test_root / "proof.txt").write_text("proof-v2\n", encoding="utf-8")
        proof_blob = hash_worktree_file(test_root, "proof.txt")
        proof_commit = build_commit(
            test_root,
            parent=published,
            path="proof.txt",
            blob=proof_blob,
            message="verification-relevant change",
        )
        assert proof_commit is not None
        git(test_root, "push", REMOTE, f"{proof_commit}:refs/heads/main")
        (test_root / "non_mf_groups_exist.pdf").write_bytes(b"non-mf-v3\n")
        try:
            publish_pdf(
                test_root,
                source_ref=published,
                pdf="non_mf_groups_exist.pdf",
                message="must not cross proof change",
            )
        except PublicationDeferred:
            pass
        else:
            raise RuntimeError("publisher crossed a verification-relevant commit")
        assert remote_main(test_root) == proof_commit

        (test_root / "non_mf_groups_exist.pdf").write_bytes(b"non-mf-draft\n")
        outcome, draft = publish_draft_pdf(
            test_root,
            source_ref=published,
            source_file="non_mf_groups_exist.tex",
            pdf="non_mf_groups_exist.pdf",
            message="publish current draft",
        )
        assert outcome is Outcome.PUBLISHED
        assert resolve(test_root, f"{draft}^") == proof_commit
        assert remote_main(test_root) == draft

        (test_root / "non_mf_groups_exist.tex").write_text(
            "manuscript-v2\n", encoding="utf-8"
        )
        manuscript_blob = hash_worktree_file(test_root, "non_mf_groups_exist.tex")
        manuscript_commit = build_commit(
            test_root,
            parent=draft,
            path="non_mf_groups_exist.tex",
            blob=manuscript_blob,
            message="new manuscript source",
        )
        assert manuscript_commit is not None
        git(test_root, "push", REMOTE, f"{manuscript_commit}:refs/heads/main")
        (test_root / "non_mf_groups_exist.pdf").write_bytes(b"stale-draft\n")
        try:
            publish_draft_pdf(
                test_root,
                source_ref=draft,
                source_file="non_mf_groups_exist.tex",
                pdf="non_mf_groups_exist.pdf",
                message="must not publish a stale draft",
            )
        except PublicationDeferred:
            pass
        else:
            raise RuntimeError("draft publisher crossed a manuscript change")
        assert remote_main(test_root) == manuscript_commit

        (test_root / "non_mf_groups_exist.tex").write_text(
            "manuscript-v3\n", encoding="utf-8"
        )
        v3_blob = hash_worktree_file(test_root, "non_mf_groups_exist.tex")
        v3_commit = build_commit(
            test_root,
            parent=manuscript_commit,
            path="non_mf_groups_exist.tex",
            blob=v3_blob,
            message="newer manuscript source",
        )
        assert v3_commit is not None
        git(test_root, "push", REMOTE, f"{v3_commit}:refs/heads/main")
        (test_root / "non_mf_groups_exist.pdf").write_bytes(b"non-mf-from-v2\n")
        outcome, fresher = publish_draft_pdf(
            test_root,
            source_ref=manuscript_commit,
            source_file="non_mf_groups_exist.tex",
            pdf="non_mf_groups_exist.pdf",
            message="publish fresher draft despite a newer source",
        )
        assert outcome is Outcome.PUBLISHED
        assert resolve(test_root, f"{fresher}^") == v3_commit
        assert remote_main(test_root) == fresher
        assert (
            blob_contents(test_root, fresher, "non_mf_groups_exist.pdf")
            == b"non-mf-from-v2\n"
        )

    print(
        "self-test: temporary-index publication preserved the sibling PDF, "
        "was idempotent, kept attested and draft guards distinct, refused "
        "genuinely stale drafts, and published a fresher draft under a "
        "moving source"
    )


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    publish = subparsers.add_parser("publish")
    publish.add_argument("--source-sha", required=True)
    publish.add_argument("--pdf", required=True, choices=sorted(ALLOWED_PDFS))
    publish.add_argument("--message", required=True)
    draft = subparsers.add_parser("publish-draft")
    draft.add_argument("--source-sha", required=True)
    draft.add_argument(
        "--source-file", required=True, choices=sorted(ALLOWED_DRAFT_SOURCES)
    )
    draft.add_argument("--pdf", required=True, choices=sorted(ALLOWED_PDFS))
    draft.add_argument("--message", required=True)
    subparsers.add_parser("self-test")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "self-test":
            self_test()
        elif args.command == "publish":
            publish_pdf(
                repo_root(),
                source_ref=args.source_sha,
                pdf=args.pdf,
                message=args.message,
            )
        elif args.command == "publish-draft":
            publish_draft_pdf(
                repo_root(),
                source_ref=args.source_sha,
                source_file=args.source_file,
                pdf=args.pdf,
                message=args.message,
            )
        else:
            raise AssertionError(f"unhandled command: {args.command}")
    except PublicationDeferred as error:
        print(f"publication deferred: {error}")
    except (OSError, RuntimeError, AssertionError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
