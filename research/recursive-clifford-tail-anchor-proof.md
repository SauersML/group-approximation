---
rg: 2
id: recursive-clifford-tail-anchor-proof
kind: route
title: Multiply CZ gates over subtrees and isolate the strict exposure input
target: recursive-clifford-tail-supplies-anchor-but-not-contraction
requires:
  - shared-gauge-cz-cancellation-needs-an-identity-outer-anchor
  - contractive-computation-ladder
---

On the dense set of elementary tensors in `(RCT1)`, only finitely many
factors of each tail product act nontrivially.  The products are isometries,
so they extend to unitary involutions.  Partitioning the descendants of `x`
into `x`, the `x0` subtree and the `x1` subtree proves `(RCT3)`, hence
`(RCT5)--(RCT6)`.

The same-gauge estimate from
`shared-gauge-cz-cancellation-needs-an-identity-outer-anchor` and the
coarse/fine trace floor give `(RCT9)`.  Substituting `(RCT8)--(RCT9)` into
`(RCT7)` gives `(RCT10)`, and `contractive-computation-ladder` gives the
energy floor.

For the obstruction, truncate the products at depth `N` and take the
negative-central regular summand of the resulting finite Clifford packet.
Every displayed recursion identity above the leaves is exact and equal-depth
subtree transport is stationary.  Since `N` is arbitrary, no strict exposure
factor can follow from the recursion identities alone.
