---
rg: 2
id: schur-wall-in-property-t-compressor-pays-hs-energy-proof
kind: route
title: Compare the packet Reynolds density with positive-density commutant no-growth
target: schur-wall-in-property-t-compressor-pays-hs-energy
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - property-t-hs-positive-density-commutant-no-growth
---

The property-T theorem bounds `tr_ad(W)<=C delta`. Combine this with `(SPW1)`
and absorb the second `C_0 delta` term. Multiplication by `4D_0^2K/3` gives
`(SPW2)`.

