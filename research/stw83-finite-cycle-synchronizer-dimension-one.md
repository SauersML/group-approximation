---
rg: 2
id: stw83-finite-cycle-synchronizer-dimension-one
kind: claim
title: A finite downstream cycle synchronizer forces nuclear dimension at most one
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
distinct_from:
  stw83-pairwise-intersecting-cycles-dimension-one: cycles may be disjoint; finitely many downstream hubs synchronize their reachability before finite entrance completion.
  stw83-finite-recurrent-core-af-feeders-dimension-one: the cyclic nucleus need not be strongly connected and the acyclic complement need not split into finite independent feeder blocks.
---

Use the standard convention that an edge travels from `s(e)` to `r(e)`.  Let
`E` be a countable row-finite graph with Condition (K) and only finitely many
cyclic vertices.  Suppose in addition that there is a finite set `H` of
vertices such that:

1. every directed cycle has a path to every `h in H`;
2. every **noncyclic** vertex which is reached by at least one directed cycle
   is reached by some `h in H`.

Then

```text
dim_nuc(C*(E)) <= 1.
```

It is enough to have one downstream hub reached by every cycle and reaching
the nonrecurrent part of the cycle-reachable region.  Several hubs permit
finitely many downstream branches.  Distinct cyclic components need not reach
one another; they need only feed the common finite family of hubs.
If `E` is acyclic, its graph algebra is AF and has nuclear dimension zero; in
the cyclic case the displayed bound is sharp.
