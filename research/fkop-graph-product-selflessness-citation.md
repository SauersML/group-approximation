---
rg: 2
id: fkop-graph-product-selflessness-citation
kind: route
title: Import the 2026 complement-connected graph-product theorem
target: graph-products-connected-complement-are-selfless
requires: []
artifacts:
  - research/artifacts/fkop-graph-product-selflessness-v3-audit-2026-08-30.md
---

Apply Flores--Klisse--O Cobhthaigh--Pagliero,
*Selfless reduced free products and graph products of C-star algebras*,
arXiv:2510.24675v3, Theorem C (Theorem 2.2), to the vertex probability
spaces

```text
(C*_r(G_v), tau_v).
```

The canonical trace is GNS-faithful and tracial, so its centralizer is the
whole algebra.  For each nontrivial `G_v`, choose `g_v != e`; then
`lambda(g_v)` is a unitary in the centralizer and
`tau_v(lambda(g_v))=0`.  Thus every hypothesis of Theorem C is met.

The standard graph-product representation identifies the reduced graph
product of these probability spaces with the reduced group C-star algebra of
the group graph product, preserving the canonical trace.  Theorem C therefore
gives complete selflessness.  Corollary D of the same paper gives simplicity,
stable rank one, strict comparison, uniqueness of the normalized 2-quasitrace,
and uniqueness of unital Jiang--Su embeddings up to approximate unitary
equivalence in the tracial case.
