# Targeted verification of the PR 211 merge

Merge: `26f3d2cbf2dd733ca5e70363927240443c9cbb10`.
PR head: `a4e3a11263a78aee82e976bbd575ed66994f61d2`.

The entire `GroupApproximation/GGT/VanKampen` source tree is identical at
these two revisions, as checked by a read-only `git diff --quiet`. The local
VanKampen source tree also agrees with the merge revision. No Git mutation
was performed for this verification.

## Fresh MSI check

The check ran on MSI `acn112`, with Lean 4.32.0, one CPU, sequential compiler
invocations, a 45-second limit per file and a 240-second limit for the run.
Sources and fresh outputs were placed in the independent directory
`/projects/standard/hsiehph/sauer354/pr211-main-26f3d2cbf`. Existing compiled
dependencies from the warm `nonsofic_existence` tree were linked into this
directory; those cached artifacts were not modified. The ordinary fleet
build lock was held during the compile run. Nothing was compiled locally.

These three merged modules passed fresh compilation:

| Module | Seconds | Result |
| --- | ---: | --- |
| `SurgeryGCellCutInclusion` | 17.718 | exit 0 |
| `SurgeryGCellCutIndices` | 13.604 | exit 0 |
| `SurgeryGCellCutContiguity` | 12.970 | exit 0 |

The next file, the existing prerequisite `PermCycleCoordinates`, stopped
the run after 12.340 seconds because the warm cache contained a stale
`PermOrbitSum.olean`, dated September 2. A separate bounded MSI signature
check established that the cached declaration was

```lean
orbitSumCongr.{u} {α β : Type u} ...
```

whereas the current `PermOrbitSum.lean` source declares independent universes:

```lean
noncomputable def orbitSumCongr {α : Type u} {β : Type w} ...
```

The compiler consequently rejected the mixed-universe application at
`PermCycleCoordinates.lean:84`. This is an identified stale dependency cache,
not a newly discovered error in one of the six merged files. The bounded
check was not expanded into rebuilding the cache's reverse dependency tree.

The per-module exit codes, elapsed times and source SHA256 values are in
`pr211-main-targeted-lean-verification-2026-09-08.json`. That JSON records the
three successes and the prerequisite failure; it is not an all-pass report.

## Prior CI evidence for all six merged modules

The PR's [targeted Lean job](https://github.com/SauersML/group-approximation/actions/runs/34140810097/job/101802136294)
completed successfully on September 7, 2026, and its log explicitly invokes
`lake lean` on each of:

- `FaceSetBoundaryCircuits.lean`
- `FaceSetBoundaryEnumeration.lean`
- `GCellCutModel.lean`
- `SurgeryGCellCutContiguity.lean`
- `SurgeryGCellCutInclusion.lean`
- `SurgeryGCellCutIndices.lean`

The six explicit check groups occur between 15:58:30 and 15:59:28 UTC. This
is compilation evidence for the PR head, whose VanKampen source tree is
identical to the merged tree. It is not a fresh full-repository check of the
merge.

The separate [full build and audit job](https://github.com/SauersML/group-approximation/actions/runs/34140810442/job/101802519210)
was not green: its log reports `scripts/Audit.lean:1338:0: error: audit
failed`, including `UNUSED` and `RFL` findings, and subsequently a runner
shutdown. The later fresh kernel recheck was skipped. The successful
targeted job must therefore not be reported as a successful full audit.
