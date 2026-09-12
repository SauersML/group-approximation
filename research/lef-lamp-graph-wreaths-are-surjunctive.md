---
rg: 2
id: lef-lamp-graph-wreaths-are-surjunctive
kind: claim
title: Every graph wreath with a LEF lamp over a surjunctive actor is surjunctive
distinct_from:
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that requires residually finite lamps and complete commutation graphs; this allows LEF lamps and every invariant commutation graph, including the empty graph.
  finitary-split-extension-surjunctivity-permanence: that supplies an abstract sufficient condition using residually finite quotient pieces; this verifies it for graph products and then removes residual finiteness of the lamp by local approximation, which does not supply those quotient pieces.
  graph-folds-over-surjunctive-groups-are-surjunctive: that treats fundamental groups of graphs of groups with a faithful vertex map; this treats graph-product lamp kernels and does not require such a graph-of-groups description.
artifacts:
  - research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md
---

Let `G` act by automorphisms on an arbitrary simplicial graph `Lambda`
with vertex set `X`, and let `A` be a group locally embeddable into finite
groups (LEF). Let `N = Lambda(A)` be the graph product of copies `A_x`,
with distinct vertex groups commuting exactly along edges in the defining
presentation. Let `G` act by `a_x -> a_(gx)`, without internal lamp twists.
Then

```text
Lambda(A) semidirect G is surjunctive iff G is surjunctive.
```

There is no assumption on the size or degrees of the graph, its number of
orbits, the stabilizers, or approximation of the action. No finite generation
or residual finiteness assumption is imposed on `A` or `G`.

For residually finite `A`, the finite induced graph-product retractions
satisfy every finitary split-extension axiom. For LEF `A`, finite partial
group tables transplant to graph wreaths with finite lamps and the same
actor and graph. Surjunctivity passes through these local embeddings by
the finite decoder-and-orphan certificate argument.

The complete graph gives permutational wreath products with LEF lamps.
The empty graph gives the free permutational lamp kernel. The result does
not cover central-sign Clifford extensions or arbitrary automorphism
actions on a graph product.
