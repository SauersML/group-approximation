---
rg: 2
id: random-private-weyl-sampling-closes-minrank-witness
kind: route
title: Combine affine condensation with uniform low-dimensional Weyl sampling
target: bounded-incidence-generator-column-minrank-witness
requires:
  - private-random-generator-columns-form-affine-rank-condenser
  - private-random-weyl-sampler-forces-growing-matrix-dimension
---

The scalar condenser supplies constant relative rank distance and the metric-
entropy theorem promotes the same private-random-pair architecture to all
exact additive matrix-valued representations.  Embedding at `N=r^2` gives
linear column length, degree-one sampled incidence, uniform base-code
spectral constants, a fixed normalized-HS threshold, and same-space dimension
lower bound `d>r=sqrt(N)`.  These are exactly the clauses of the target for
the allowed exact-additivity alternative.
