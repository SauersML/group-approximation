---
rg: 2
id: affine-simplex-riesz-cb-proof
kind: route
title: Split the two affine weights into coordinate and constant matching masks
target: affine-simplex-riesz-inverse-is-uniformly-cb
requires: []
---

Equation `(ASR3)` follows from the two nonzero weights of the affine code.
For a fixed output index `i`, apply the complete contractions to the column
`(b_(i,j))_j` and then sum its `L` entries.  The summation map from an
unnormalized `L`-column has norm `sqrt(L)`, while the coefficient is `2/L`.
After combining the output `i`-column, the input normalization `L^-2` and
output normalization `L^-1` cancel the remaining `sqrt(L)`, giving norm at
most two.  The constant matching term is identical with coefficient `1/L`
and gives norm at most one.  Triangle inequality proves the column bound
three; applying it to adjoints proves the row bound.
