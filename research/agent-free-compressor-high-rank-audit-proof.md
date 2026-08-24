---
rg: 2
id: agent-free-compressor-high-rank-audit-proof
kind: route
title: Combine the all-rank product model with the normalized-versus-Frobenius scaling barrier
target: agent-free-compressor-high-rank-stability-does-not-authenticate
requires:
  - agent-free-compressor-named-row-retains-complement-gauge
  - agent-bcl-two-kazhdan-route-misses-group-and-metric
---

The first assertion is immediate from `(CGP1)--(CGP3)`, which are valid for
every `N>=3`.  The remaining assertions are the norm audit already used in
the repository's normalized-HS stability forks: the available 2-Kazhdan
splitting theorem assumes a submultiplicative unnormalized norm, whereas the
normalized matrix Hilbert--Schmidt norm loses the factor `sqrt(d)` in
`(HRS1)`.  Since the BCL microstate dimensions are unbounded, no fixed
Frobenius correction radius follows.  Property `(T)` alone is a degree-one
spectral-gap statement and supplies no correction of approximate
multiplication.  Thus none of these theorems contradicts the exact all-rank
countermodel or proves `(ACP6)`.
