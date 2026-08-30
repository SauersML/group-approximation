---
rg: 2
id: graph-products-no-universal-vertex-selfless-criterion
kind: claim
title: Exact selflessness criterion for graph products without universal vertices
distinct_from:
  graph-products-connected-complement-are-selfless: that theorem assumes the complement is connected; this theorem permits arbitrarily many complement components and gives an exact criterion.
  stw91-cograph-products-preserve-selflessness: that theorem assumes exact selfless vertex algebras and a P4-free graph; this theorem permits arbitrary nontrivial vertex groups and arbitrary graphs without universal vertices.
  stw99-problem-xci-cstar-simple-selfless: this completely settles XCI for the stated graph-product class, not for arbitrary C-star-simple groups.
artifacts:
  - research/artifacts/stw91-graph-component-selflessness-audit-2026-08-30.md
---

Let `Gamma` be a countable simple graph with at least two vertices and no
universal vertex.  Equivalently, the complement graph `Gamma^c` has no
isolated vertex.  Label its vertices by nontrivial countable groups `(G_v)`,
and let

```text
P=graph_product_Gamma G_v.
```

The following are equivalent:

1. `P` is C-star-simple.
2. `(C*_r(P),tau_P)` is selfless.
3. There is no two-vertex connected component `{v,w}` of `Gamma^c` for which
   `G_v ~= C_2 ~= G_w`.

When these conditions hold and `Gamma^c` has only finitely many connected
components, `C*_r(P)` is completely selfless.

Moreover, if every `G_v` is a nontrivial C-star-simple group, then `C*_r(P)`
is completely selfless without any finiteness assumption on the number of
complement components.

Hence XCI and XC both have positive answers for every C-star-simple graph
product with no universal vertex.