# docbuild/

A second, deliberately separate Lake project whose only job is to build the
API reference for `GroupApproximation` with
[doc-gen4](https://github.com/leanprover/doc-gen4).

It is three files and no source: `lakefile.toml`, `lean-toolchain`, and a
committed `lake-manifest.json`.  The manifest is the point.  doc-gen4 pulls in
its own dependency graph, and resolving that graph fresh would let a doc-only
dependency bump change what the documentation says about a proof that has not
moved.  Pinning it here, in a project the corpus build never loads, keeps the
documentation toolchain out of the root `lakefile.toml` while still committing
it: the reference is reproducible, and a doc-gen4 update is a reviewable diff
rather than a silent re-resolution.

## Who uses it

- `.github/workflows/docs.yml` — weekly (Sundays 06:00 UTC) and on demand.
  It builds `GroupApproximation:docs` with `working-directory: docbuild`,
  keyed on `hashFiles('docbuild/lean-toolchain', 'docbuild/lake-manifest.json')`,
  and publishes the result to the `api-docs` branch.  `cairn-site.yml` folds
  that branch into the published site under `/api/`.
- `.github/workflows/prover.yml` — excludes these files from the paths that
  trigger the prover gate; a doc-dependency bump proves nothing about the
  corpus and must not spend a runner on it.
- `scripts/advance_verified_branch.py` and `scripts/release_manifest.py` —
  both name the three files explicitly.

## What it is not

It builds no Lean source of its own, is not a `require` of the root project,
and never runs as part of the prover gate.  Deleting it does not break the
build; it breaks the published API reference, and takes the pinned doc-gen4
graph with it.
