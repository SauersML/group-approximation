---
rg: 2
id: graph-product-closure-from-product-closure
kind: route
title: Peel a vertex off a graph product and fold the amalgam into the product of its two retractions
target: graph-products-of-surjunctive-groups-are-surjunctive
requires:
  - finite-direct-products-of-surjunctive-groups-are-surjunctive
  - graph-folds-over-surjunctive-groups-are-surjunctive
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Section 3(b) of the artifact.

**Finite graphs**, by induction on the number of vertices:
- Decompose `Γ(X) = Γ(st v) *_(Γ(lk v)) Γ(X∖v)` with `Γ(st v) = G_v x Γ(lk v)`. Both edge maps are
  injective.
- The retractions `ρ_(st v)` and `ρ_(X∖v)` are homomorphisms. They restrict to the identity on the two
  vertex groups, so `f = (ρ_(st v), ρ_(X∖v))` is injective on each.
- The target `Γ(st v) x Γ(X∖v)` is surjunctive by induction and product closure.
- The graph-fold theorem gives surjunctivity of `Γ(X)`.

**Infinite graphs.** `Γ(X)` is the directed union of its finite full subgraph products. The
rectangle-clause axiomatization preserves surjunctivity under directed colimits.

**Cycle.** This route and `product-closure-from-graph-product-closure` form a deliberate equivalence
cycle.
