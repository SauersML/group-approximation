---
rg: 2
id: bounded-degree-extraspecial-packets-have-fixed-reuse-model
kind: claim
title: Bounded-degree extraspecial packet complexes have a fixed reuse model
distinct_from:
  bounded-neighbor-pauli-needs-growing-equality-components: that colors individual signed Pauli generators by distance-two colors; this colors whole finite extraspecial packets connected by independence edges.
  isomorphic-extraspecial-packet-complex-folds: that handles full-packet transport identifications by finite holonomy; this handles commuting/independence attachments without identifying neighboring packets.
---

Fix a finite extraspecial packet `K` with central involution `J` and a unitary
representation of dimension `d_K` in which `J=-I`.  Put one copy `K_v` at
every vertex of a graph `Lambda` of maximum degree `Delta`, identify all
copies of `J`, and impose that adjacent vertex packets commute elementwise.

The resulting packet group has an exact unitary representation of dimension

```text
d_K^(Delta+1)                                                   (BEP1)
```

with the common mark `J=-I`, independent of `|V(Lambda)|`.

Indeed, properly color `Lambda` with at most `Delta+1` colors and map every
packet of one color to the same tensor factor.  Adjacent vertices have
different colors and therefore commute, while nonadjacent packets are free
to reuse a factor.

Consequently a bounded-degree small-cancellation skeleton of fixed finite
packets does not retain an unbounded Pauli dimension witness.  To defeat
reuse it needs unbounded chromatic/interaction complexity, growing equality
or code components, or attachments carrying genuinely increasing packet
rank.

