---
rg: 2
id: fpbs-stationary-set-gap-from-green-visit
kind: route
title: Finite expected simple-random-walk visits are almost surely finite visits along a walk range
target: fpbs-stationary-set-relative-gap-universal
requires:
  - fpbs-green-visit-criterion-universal
---

`fpbs-green-visit-criterion-universal` gives `p > p_c` with
`E #{n : X_n in C_e} < infinity` for the simple random walk `X_n`, independent
of the percolation. A nonnegative random variable with finite expectation is
a.s. finite. So the walk range of `mu = Unif(S)` is an independent stationary
set of type (W) with `V < infinity` a.s. at `p`. ∎

This records that the new hole is implied by the weakest green-visit kernel.
