---
rg: 2
id: graph-products-of-surjunctive-groups-are-surjunctive
kind: claim
title: Every graph product of surjunctive groups is surjunctive
distinct_from:
  graph-folds-over-surjunctive-groups-are-surjunctive: that needs a homomorphism to a given surjunctive group injective on each vertex group of a graph of groups; this asks for all right-angled graph products of surjunctive vertex groups, free and direct products included, with no target group supplied.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

**OPEN.** Let `X` be a simplicial graph with a surjunctive group `G_v` at each vertex. Then the graph
product `Γ(X)` is surjunctive.

**Special cases.** The edgeless graph gives free products and the complete graph gives direct products.

**Equivalence with binary products.**
- `graph-product-closure-from-product-closure` proves this claim from
  `finite-direct-products-of-surjunctive-groups-are-surjunctive`, using the amalgam decomposition
  `Γ(X) = (G_v x Γ(lk v)) *_(Γ(lk v)) Γ(X∖v)`, the retractions onto full subgraphs, and graph folds.
- `product-closure-from-graph-product-closure` gives the converse.

The two routes form a deliberate cycle.

## Attempts

- **Graph folds need a target.** The retraction map
  `(ρ_(st v), ρ_(X∖v)): Γ(X) -> Γ(st v) x Γ(X∖v)` is injective on both vertex groups. Its target is
  surjunctive only if products are, so the route stops exactly at binary products.
- **Proved piece.** For a single LEF vertex group adjoined freely, the free-product case is
  `free-centralizer-amalgams-are-surjunctivity-inert` with trivial amalgamated subgroup. With LEF
  factors, products follow from `products-with-lef-factors-preserve-surjunctivity`. General graph products
  of one surjunctive and several LEF vertex groups are not settled: the induction produces products of two
  non-LEF pieces.
