---
rg: 2
id: stw83-finite-kirchberg-core-circle-quotient-dimension-one
kind: claim
title: A finite essential Kirchberg-core graph with a circle quotient has nuclear dimension one
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `F` be a finite directed graph whose vertex set is a disjoint union
`V_0 disjoint_union V_1 disjoint_union V_2` with all of the following properties.

1. `V_0` is the saturation of the vertex set of a nonempty finite disjoint
   union of simple cycles, and its induced graph is the corresponding disjoint
   union of simple cycles.
2. The induced graph on `V_1` is acyclic.
3. The induced graph on `V_2` is strongly connected, has an edge, and is not a
   simple cycle.
4. There is no path from `V_i` to `V_j` when `i>j`.
5. Every vertex in `V_0 union V_1` has a path to `V_2`.

Then

```text
dim_nuc(C*(F)) = 1.
```

More precisely, `C*(F)` is an essential extension of an algebra stably
isomorphic to a finite direct sum of circle algebras by a stable Kirchberg ideal.
