---
rg: 2
id: graph-products-noncomplete-selfless-criterion
kind: claim
title: Every C-star-simple graph product over a noncomplete graph is selfless
distinct_from:
  graph-products-no-universal-vertex-selfless-criterion: that theorem excludes universal vertices; this theorem permits arbitrarily many universal vertices and arbitrary C-star-simple groups on them.
  graph-products-connected-complement-are-selfless: that theorem assumes one connected complement component; this theorem permits singleton and nonsingleton components and uses one completely selfless component to absorb the entire remainder.
  stw99-problem-xci-cstar-simple-selfless: a one-vertex complete graph is an arbitrary group, so the universal root remains open even though every noncomplete graph-product instance is settled.
artifacts:
  - research/artifacts/stw91-universal-vertex-absorption-audit-2026-08-30.md
---

Let Gamma be a countable simple graph that is not complete, label its vertices
by nontrivial countable groups (G_v), and let

    P = graph_product_Gamma G_v.

The following are equivalent:

1. P is C-star-simple.
2. (C*_r(P),tau_P) is selfless.
3. Every universal vertex v of Gamma has C-star-simple vertex group G_v, and
   there is no two-vertex connected component {v,w} of the complement graph
   Gamma^c with G_v isomorphic to C_2 and G_w isomorphic to C_2.

When these conditions hold, C*_r(P) has stable rank one and strict
comparison; its canonical trace is its unique trace and unique normalized
2-quasitrace.

Thus STW Problems XCI and XC both have positive answers for every graph
product whose defining graph has at least one missing edge. This includes
arbitrarily many universal vertices. No exactness or selflessness hypothesis
is imposed on their C-star-simple vertex groups.
