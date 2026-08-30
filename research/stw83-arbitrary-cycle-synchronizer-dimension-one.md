---
rg: 2
id: stw83-arbitrary-cycle-synchronizer-dimension-one
kind: claim
title: Finite cycle synchronizers allow sinks and infinite emitters
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
distinct_from:
  stw83-finite-cycle-synchronizer-dimension-one: that is the row-finite completion theorem; this result retains its hypotheses through a carefully ordered Drinen--Tomforde desingularization.
---

Let `E` be an arbitrary countable directed graph with Condition (K), allowing
sinks and infinite emitters.  Use the standard edge convention.  Assume that
the cyclic vertices and edges belonging to cycles lie in a finite subgraph and
that a finite vertex set `H` satisfies:

1. every directed cycle has a path to every vertex of `H`;
2. every vertex reached by a cycle is reached by some vertex of `H`.

Then

```text
dim_nuc(C*(E)) <= 1.
```

At an infinite emitter which lies on a cycle, place first the finitely many
emitted edges belonging to cycles in the desingularization ordering.  No
cofinal abundance assumption is required.
