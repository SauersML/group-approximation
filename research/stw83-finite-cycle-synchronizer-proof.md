---
rg: 2
id: stw83-finite-cycle-synchronizer-proof
kind: route
title: Retain paths through finitely many hubs before adding new sinks
target: stw83-finite-cycle-synchronizer-dimension-one
requires:
  - stw83-finite-source-dichotomy-dimension-one
---

Translate the finite theorem and entrance completion of
Faurot--Schafhauser into the standard edge convention.  Their sources become
sinks, and "a source connects to a cycle" becomes "a cycle reaches the sink".
Thus their finite theorem applies when each sink is reached by every cycle or
by none.

Fix once and for all a finite subgraph `L` containing the cyclic nucleus, `H`,
and a path from every simple cycle to every hub.  Starting from an arbitrary
finite subgraph `F`, adjoin `L`.  For every vertex `v` now present which is
reached by a cycle, choose a hub `h` and adjoin a path `h->v`.  Call the
resulting finite graph `G`.  Every vertex on an added hub path is already
reached inside `G` by every cycle: follow the retained cycle-to-hub path and
then the appropriate initial segment.  Every other vertex of `G` is reached by
no ambient cycle.

Take the Faurot--Schafhauser entrance completion, in the translated
convention: whenever `G` contains an edge emitted at `w`, include all ambient
edges emitted at `w` and their range vertices.  Row-finiteness makes the
completion `G_tilde` finite.  A newly added vertex outside `G` is a sink, so no
new cycle passes through it.  Any old sink was already internally reached by
every cycle or by none.  A new sink is internally reached by every cycle when
one of its predecessors is cycle-reachable, and is reached by no cycle when
all its predecessors are no-cycle vertices.  Hence every sink of `G_tilde`
satisfies the finite dichotomy and

```text
dim_nuc(C*(G_tilde)) <= 1.                            (1)
```

The completion has Condition (K), and its canonical generator map into
`C*(E)` is injective by Faurot--Schafhauser, Proposition 2.3.  Enumerating the
vertices and edges of `E` and repeating the construction, each time starting
with the preceding completion, gives

```text
C*(E) = direct_limit_n C*(G_tilde_n).
```

Inductive-limit permanence and (1) prove the upper bound without an extension
loss.  In the cyclic case `C*(E)` is not AF, so the dimension is exactly one.
