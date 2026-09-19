---
rg: 2
id: stw83-kirchberg-core-circle-crowns-dimension-one
kind: claim
title: Countably many simple circle crowns over one finite Kirchberg core have nuclear dimension one
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `E` be a countable row-finite graph assembled as follows, with all vertex
sets mentioned below disjoint.

- `K` is a fixed finite strongly connected subgraph with an edge which is not a
  simple cycle.
- For each `m>=1`, `C_m` is a finite simple directed cycle and `D_m` is a finite
  acyclic connector graph.
- Every vertex of `C_m union D_m` has a path, staying inside
  `C_m union D_m union K`, to `K`; at least one edge leaves `C_m` toward
  `D_m union K`.
- Edges emitted by `D_m` stay in `D_m` or enter `K`; in particular, no connector
  edge returns to `C_m`.  Other edges outside `K` stay in their own block or
  enter `K`.  There are no edges from `K` to a block and no edges between
  distinct blocks.

Then

```text
dim_nuc(C*(E)) = 1.
```

This is genuinely outside both previously recorded broad classes.  Each `C_m`
has an exit but only one return cycle, so `E` fails Condition (K), and the cycle
with an exit gives an infinite projection, so `C*(E)` is not stably finite.
