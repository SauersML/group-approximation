---
rg: 2
id: stw83-finite-recurrent-core-af-feeders-dimension-one
kind: claim
title: A fixed finite recurrent core absorbs countably many acyclic feeder blocks with one color
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
distinct_from:
  stw83-pairwise-intersecting-cycles-dimension-one: that theorem forces finite source control because cycles intersect; this permits disjoint cycles inside a fixed strongly connected core and obtains source control by including the entire recurrent core in every finite stage.
---

Let `E` be a countable row-finite graph with a fixed finite strongly connected
subgraph `K` which has Condition (K), has an edge, and is not a simple cycle.
Suppose every vertex outside `K` lies in one of countably many finite acyclic
blocks `D_m`, every such vertex reaches `K`, edges outside `K` stay within their
block or enter `K`, and there are no edges from `K` to the blocks or between
distinct blocks.  Then

```text
dim_nuc(C*(E)) = 1.
```

Cycles in `K` need not intersect pairwise.  Thus this gives a new uniform
AF-by-O-infinity color-reuse class beyond the pairwise-cycle criterion.
