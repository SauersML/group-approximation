#!/usr/bin/env python3
"""Emit a manifest binding a release archive to what produced it.

An archive of this repository, on its own, proves nothing about its origin:
no commit, no toolchain, no link between the committed PDF and the committed
sources.  This script prints (or writes, with --write) a JSON manifest
carrying:

  * the repository commit, the clean-checkout attestation, and the generated
    build-tree changes,
  * the Lean toolchain and the Mathlib commit from the manifest,
  * a SHA-256 for every Lean source, the manuscript, generated docs, release
    workflows, certificate-generation inputs, and the compiled PDF.

A reviewer holding the archive and the manifest can verify every file
against it; a reviewer holding only the archive can at least see which
commit to fetch and diff.  Run at release time:

    python3 scripts/release_manifest.py --write   # writes metadata/RELEASE_MANIFEST.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def _git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=REPO, check=True,
                          capture_output=True, text=True).stdout.strip()


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def build_manifest(*, commit: str | None = None,
                   kernel_audit_run_id: str | None = None,
                   pdf: Path | None = None,
                   source_checkout_clean: bool = False,
                   publication_run_id: str | None = None,
                   texlive_image: str | None = None) -> dict:
    manifest_path = REPO / "lake-manifest.json"
    mathlib = None
    if manifest_path.is_file():
        for pkg in json.loads(manifest_path.read_text())["packages"]:
            if pkg.get("name") == "mathlib":
                mathlib = pkg.get("rev")

    files = sorted(
        p for pattern in ("GroupApproximation/**/*.lean", "GroupApproximation.lean",
                          "scripts/**/*", "docs/*", "metadata/*", ".github/workflows/*.yml",
                          "experiments/sl3-p13-reductions-complete.json",
                          "experiments/sl3-sos-radius0-certificate.json",
                          "experiments/sl3-sos-radius0-certificate.npz",
                          "experiments/sl3_p13_certificate_lean_generator.py",
                          "experiments/sl3_p13_hodge_lean_generator.py",
                          "experiments/sl3_p13_pair_table_generator.py",
                          "experiments/sl3_p13_relator_replay.py",
                          "experiments/sl3_p13_replay_lean_generator.py",
                          "docbuild/lakefile.toml", "docbuild/lean-toolchain",
                          "docbuild/lake-manifest.json",
                          "property_tt_leavitt.tex", "property_tt_leavitt.pdf",
                          "non_mf_groups_exist.tex", "non_mf_groups_exist.pdf",
                          "README.md", "CITATION.cff", "lakefile.toml",
                          "lean-toolchain", "lake-manifest.json")
        for p in REPO.glob(pattern)
        if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc"
    )

    if pdf is not None:
        resolved = pdf if pdf.is_absolute() else REPO / pdf
        if resolved.is_file() and resolved not in files:
            files.append(resolved)
            files.sort()

    generated_changes = [line[3:] for line in
                         _git("status", "--porcelain").splitlines()]

    return {
        "commit": commit or _git("rev-parse", "HEAD"),
        "source_checkout_clean_before_generation": source_checkout_clean,
        "generated_worktree_changes": generated_changes,
        "kernel_audit_workflow_run_id": kernel_audit_run_id,
        "publication_workflow_run_id": publication_run_id,
        "texlive_image": texlive_image,
        "build_command": "lake build && lake env lean scripts/Audit.lean && "
                         "lake env lean scripts/Signatures.lean && "
                         "lake env leanchecker --fresh GroupApproximation",
        "lean_toolchain": (REPO / "lean-toolchain").read_text().strip(),
        "mathlib_commit": mathlib,
        "files": {str(p.relative_to(REPO)): _sha256(p) for p in files},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true",
                    help="write metadata/RELEASE_MANIFEST.json instead of stdout")
    ap.add_argument("--commit", help="source commit recorded by CI")
    ap.add_argument("--kernel-audit-run-id",
                    help="workflow run that built and kernel-audited this revision")
    ap.add_argument("--pdf", type=Path, help="PDF artifact to hash")
    ap.add_argument("--source-checkout-clean", action="store_true",
                    help="record that CI asserted a clean checkout before generation")
    ap.add_argument("--publication-run-id",
                    help="workflow run that built and attested the PDF")
    ap.add_argument("--texlive-image",
                    help="digest-pinned TeX Live image used for the PDF")
    ap.add_argument("--output", type=Path,
                    help="write to this path instead of stdout")
    args = ap.parse_args()

    manifest = build_manifest(commit=args.commit,
                              kernel_audit_run_id=args.kernel_audit_run_id,
                              pdf=args.pdf,
                              source_checkout_clean=args.source_checkout_clean,
                              publication_run_id=args.publication_run_id,
                              texlive_image=args.texlive_image)
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.write or args.output:
        out = args.output or (REPO / "metadata" / "RELEASE_MANIFEST.json")
        if not out.is_absolute():
            out = REPO / out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding="utf-8")
        try:
            display = out.relative_to(REPO)
        except ValueError:
            display = out
        print(f"wrote {display} "
              f"({len(manifest['files'])} files, commit {manifest['commit'][:12]}, "
              f"source-clean={manifest['source_checkout_clean_before_generation']})")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
