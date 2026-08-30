---
rg: 2
id: stw83-stably-finite-graphs-dimension-one-proof
kind: route
title: Apply the large-abelian-isotropy graph-groupoid theorem
target: stw83-stably-finite-graphs-dimension-one
requires: []
---

An Huef and Williams, Theorem 6.1 in
[Nuclear dimension of groupoid C*-algebras with large abelian isotropy](https://arxiv.org/abs/2412.10241),
proves the estimate for a row-finite graph with no sources when no return path
has an entrance, and states the resulting conclusion for every stably finite graph
C*-algebra.  Their proof identifies the graph algebra with its amenable graph-
groupoid algebra, uses openness of the isotropy subgroupoid, and obtains

```text
(1+1)(0+1)(0+1)-1 = 1
```

from their groupoid nuclear-dimension estimate.  Their Remark 6.2 cites the graph
equivalences

```text
stably finite  <=>  AF-embeddable  <=>  no return path has an entrance.
```

Their final example contains a return path but is not AF, so its nuclear dimension
is exactly one rather than zero.
