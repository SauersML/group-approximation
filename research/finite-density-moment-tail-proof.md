---
rg: 2
id: finite-density-moment-tail-proof
kind: route
title: Split the noise, tensorize finite-space hypercontractivity, and apply Holder
target: finite-density-moments-control-noisy-tails
requires: []
artifacts:
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
---

Theorem 1 of the artifact proves the claim in all dimensions. Set
`s=sqrt(rho)`. A compactness argument, including the Taylor expansion near
constant functions, gives a single-site `L2 -> Lp` contraction for `T_s`
with `p>2`; mixed-norm Minkowski tensorizes it. Choose an integer `q>=2`
with `2q/(q-1)<=p`. The inner half of the noise gives squared tail norm at
most `rho^(d+1)||F||_2^2`, the outer half gives the needed higher norm,
and Holder against `1_E dnu/dU_N` gives the result. No computational
exhaustion or conjectural hardness result is used.
