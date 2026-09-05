# FLT vendoring record — one file

This directory holds **one** file, vendored from
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
(Apache License 2.0, same licence as this repository's root `LICENSE`):

- `Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean` — Madison Crim's
  `FLT/Mathlib/Algebra/IsDirectLimit.lean`: the predicate `IsDirectLimit f g`
  on a directed system, with `IsDirectLimit.lift`, `lift_of`, the equivalence
  `IsDirectLimit.Equiv` between any two direct limits of one system, and the
  `Module` versions. 153 lines; its only import is `Mathlib`.

## Why only one file

`GroupApproximation/Analysis/SequentialGroupColimitDirectLimit.lean` needs the
universal property of a direct limit, so that a homomorphism out of
`K₁(A) = colim_n U(Mₙ(A))/U₀(Mₙ(A))` can be produced from a compatible family
on the levels. That is the whole dependency.

The tree originally landed here in full: **2344 `.lean` files, 20 MB**, for
that one 7 KB file. That is not free. Every `scripts/remote-build.sh`
invocation rsyncs `--include='*.lean'` over the working tree, so the surplus
was re-scanned on every build by every lane; while it was being deleted
concurrently, rsync emitted hundreds of "file has vanished" errors into every
lane's build log. It also inflated `scripts/check.py --list-orphans` from 287
to 2632, because that gate walks the filesystem rather than `git ls-files`, so
an untracked tree counts as corpus orphans.

Trimmed to the single required file on 2026-09-05. `.gitignore` excludes
everything else under this directory, so a future bulk copy cannot be committed
by the snapshot sweep.

## What the rest of that repository does NOT contain

Assessed 2026-09-05 (see `notes/flt-repo-assessment-2026-09-05.md`): zero files
mentioning Steenrod squares, Chern classes, Stiefel–Whitney classes,
topological K-theory, Borsuk–Ulam, vector bundles, homotopy groups, or complex
projective space. Its large `Cohomology`/`singular` hit counts are Galois and
group cohomology and singular points of schemes. Nothing else there is useful
to this campaign — do not re-vendor it in bulk.
