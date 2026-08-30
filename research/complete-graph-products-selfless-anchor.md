---
rg: 2
id: complete-graph-products-selfless-anchor
kind: claim
title: Complete graph products with one completely selfless anchor satisfy XCI
distinct_from:
  graph-products-noncomplete-selfless-criterion: that theorem gets its anchor from a missing edge; this theorem treats the complementary complete-graph boundary by assuming one vertex algebra is already completely selfless.
  stw90-php-times-cstar-simple-is-strict-comparison: that theorem treats two group factors and assumes a PHP anchor; this theorem permits any completely selfless anchor and countably many arbitrary C-star-simple remaining factors.
  complete-selflessness-is-tensor-stable: that theorem requires both tensor factors to be completely selfless to preserve complete selflessness; this theorem needs only one completely selfless factor and concludes ordinary selflessness.
artifacts:
  - research/artifacts/stw91-complete-graph-anchor-audit-2026-08-30.md
---

Let Gamma be a nonempty countable complete graph, label its vertices by
nontrivial countable groups (G_v), and suppose that for some vertex v_0,

    (C*_r(G_(v_0)),tau_(v_0))

is completely selfless. For the graph product

    P = graph_product_Gamma G_v
      = direct_sum_v G_v,

the following are equivalent:

1. P is C-star-simple.
2. (C*_r(P),tau_P) is selfless.
3. Every vertex group G_v is C-star-simple.

No exactness hypothesis is imposed on any of the remaining vertex groups.

There is also an exact ordinary-anchor variant: if the distinguished vertex
algebra is selfless, every other vertex group is C-star-simple, and every
other reduced vertex algebra is exact, then C*_r(P) is selfless.

If Gamma is finite and every reduced vertex algebra is completely selfless,
then C*_r(P) is completely selfless. For a countably infinite complete graph,
one completely selfless vertex still gives the ordinary selflessness
conclusion above.

In every selfless case, C*_r(P) has stable rank one and strict comparison,
and its canonical trace is its unique trace and unique normalized
2-quasitrace.
