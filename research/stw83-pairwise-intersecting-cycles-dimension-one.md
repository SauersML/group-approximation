---
rg: 2
id: stw83-pairwise-intersecting-cycles-dimension-one
kind: claim
title: Pairwise-intersecting cycles force nuclear dimension at most one under Condition (K)
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `E` be a countable directed graph with Condition (K), allowing sinks and
infinite emitters.  Suppose every two cycles in `E` have a common vertex.  Then

```text
dim_nuc(C*(E)) <= 1.
```

The condition is vacuous for an acyclic graph, in which case `C*(E)` is AF and
has nuclear dimension zero.  The cyclic case includes countably infinite,
non-stably-finite graphs: for example, one may take two loops at a common vertex
and attach countably many acyclic vertices and edges without creating a new cycle.
