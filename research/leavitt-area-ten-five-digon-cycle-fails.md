---
rg: 2
id: leavitt-area-ten-five-digon-cycle-fails
kind: claim
title: The five-digon decagon cycle does not produce an area-ten Leavitt kernel disk
artifacts:
  - research/artifacts/leavitt-area-ten-structural-audit-2026-08-21.md
distinct_from:
  leavitt-area-ten-short-atlas-partitions: that lists all eleven topological types; this eliminates the most degenerate and most likely disk type by restoring exact labels.
---

For the partition `(2,2,2,2,2,10,10)`, the five vertex-disjoint digons
exhaust all ten vertices.  Their remaining external edges form a five-cycle,
so the ribbon core is unique up to reflection.

There is no assignment of relator orientations and `R_0/R_1` colors for
which the five digon labels are trivial in `Q`, one decagon is trivial in
`Q`, and the other is a nontrivial coefficient boundary.  The exact finite
audit checks all `3126` sign-compatible edge orientations and all colorings,
rejecting inverse-relator dipoles, and returns zero solutions.

Therefore any area-ten short-atlas disk must lie in one of the other ten
partitions in `(ATP1)` and has at most four digons.

