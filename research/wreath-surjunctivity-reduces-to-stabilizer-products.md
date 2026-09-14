---
rg: 2
id: wreath-surjunctivity-reduces-to-stabilizer-products
kind: claim
title: A permutational wreath product is surjunctive exactly when every lamp power times its stabilizer intersection is
distinct_from:
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that proves surjunctivity for residually finite lamps over any surjunctive base; this allows arbitrary lamps and reduces surjunctivity of the wreath product exactly to surjunctivity of the stabilizer products A^U x G_U.
  finitary-split-extension-surjunctivity-permanence: that needs residually finite site projections on a split kernel; this treats wreath kernels whose lamps need not be residually finite, at the price of products in the hypothesis.
  lef-lamp-graph-wreaths-are-surjunctive: that covers graph wreath products with LEF lamps; this is the permutational wreath product with arbitrary lamps.
artifacts:
  - research/artifacts/wreath-surjunctivity-stabilizer-products-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a group, `X` a left `G`-set, `A` any group, and
`W = A wr_X G`. For finite `U` in `X`, let `G_U` be the pointwise stabilizer of `U`,
with `G_(empty) = G`. Then

    W is surjunctive  <=>  A^U x G_U is surjunctive for every finite U in X.

Consequences:

- `A wr G`, with the regular action, is surjunctive iff `G` and every finite power
  `A^n` are surjunctive.
- If surjunctivity is closed under finite direct products, then `A wr_X G` is
  surjunctive whenever `A` and `G` are, for every action. So closure under
  permutational wreath products reduces to closure under finite direct products,
  which is open.
- Sofic lamps over sofic bases give surjunctive wreath products for every action,
  even nonsofic ones.
- The simple wreath shift `S wr Z` inside the Fournier--Facio group
  (`fournier-facio-group-contains-simple-wreath-shift`) is surjunctive iff every
  `S^n` is.

Proof: `wreath-surjunctivity-reduces-to-stabilizer-products-proof`.
