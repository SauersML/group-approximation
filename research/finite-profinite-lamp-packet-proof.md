---
rg: 2
id: finite-profinite-lamp-packet-proof
kind: route
title: Read fixed-point fractions as permutation characters and pass to CE limits
target: finite-profinite-lamp-packets-cannot-carry-manzoor-trace
requires:
  - non-cohyperlinear-irs-exists
  - random-coset-lamp-correlations-realize-every-irs-character
---

The normalized trace of a permutation matrix is its fixed-point fraction,
proving `(FPL1)`.  Applying `(RCL3)` separately to every diagonal block proves
`(FPL2)`.  Countable tracial direct sums of matrix algebras are hyperfinite.

For a profinite inverse system, a point is fixed in the inverse limit exactly
when every finite-level coordinate is fixed.  The corresponding measurable
sets decrease with `n`, so probability continuity gives `(FPL3)`.  Pointwise
limits of finite-dimensional characters yield embeddings into a tracial
matrix ultraproduct.  Both constructions therefore produce Connes-embeddable
GNS traces, contradicting the established Manzoor character if they were to
equal it.

