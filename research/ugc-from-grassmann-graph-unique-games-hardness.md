---
rg: 2
id: ugc-from-grassmann-graph-unique-games-hardness
kind: route
title: Unique-games hardness restricted to Grassmann constraint graphs is unique-games hardness
target: unique-games-conjecture
requires: [unique-games-hard-on-non-sse-grassmann-constraint-graphs]
---

This is immediate. The prerequisite gives, for every `eta, delta > 0`, a
polynomial-time reduction from 3SAT to unique games with YES value `>= 1 - eta`
and NO value `<= delta`. The outputs are unique games, and the restriction on
the constraint graph is only extra information. So `Gap-UG[1 - eta, delta]` is
NP-hard for every `eta, delta > 0`, which is UGC. The graph restriction matters
for the relation to SSEH, not for this implication.
