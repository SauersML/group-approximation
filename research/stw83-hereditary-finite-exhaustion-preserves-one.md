---
rg: 2
id: stw83-hereditary-finite-exhaustion-preserves-one
kind: claim
title: A finite hereditary graph exhaustion preserves a uniform nuclear-dimension-one bound
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `E` be a countable row-finite directed graph, using the convention that an
edge runs from its source to its range.  Suppose

```text
H_1 subset H_2 subset ... subset E^0,      union_n H_n = E^0,
```

where every `H_n` is finite and hereditary: an edge whose source lies in `H_n`
also has range in `H_n`.  Write `E_n` for the induced graph on `H_n`.  Then the
canonical generator maps are injective and

```text
C*(E) = direct_limit_n C*(E_n).
```

In particular, if `dim_nuc(C*(E_n)) <= 1` for every `n`, then
`dim_nuc(C*(E)) <= 1`.

This statement requires row-finiteness.  If a vertex is an infinite emitter in
`E` but becomes a finite emitter in a finite subgraph, that subgraph imposes a
Cuntz--Krieger equality which need not hold in `C*(E)`.
