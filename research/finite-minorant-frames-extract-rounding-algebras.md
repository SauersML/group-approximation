---
rg: 2
id: finite-minorant-frames-extract-rounding-algebras
kind: route
title: A finite minorant preserves Kraus mass and bounds the atomic source algebra
target: bounded-kraus-minorants-force-channel-rounding
requires: []
artifacts:
  - research/artifacts/bounded-kraus-minorant-channel-rounding-2026-09-08.md
---

Order orthogonal Kraus vectors for `P_n` by their squared `L^2`
norms. The tail frame has operator norm at most `1/(k+1)`;
Bessel's inequality and both bistochastic marginals bound the
product-frame tail by `2/(k+1)`. Haar RMS defect therefore makes
the limiting atomic frame equal its product frame.

Taking traces forces the limiting Kraus marginals to be the same
projection `p`. The fixed finite Kraus family `b_1,...,b_r` of the
minorant survives in the ultraproduct with both marginal sums one.
Frame domination puts every `b_j` in `pMp`, forcing `p=1`.

The stationary trace-class frame then commutes with left and right
multiplication by the Kraus algebra `B`. Its support contains the
minorant vectors; these belong to `B`, and left multiplication puts
`sum_j b_j* b_j=1` in the support. Thus its support is `L^2(B)`.
Compactness makes `B` a countable product of finite matrix blocks.
On a block of degree `m` and trace weight `t`, its scalar is `t/m^2`.

Compress the minorant frame to finitely many blocks and conjugate
by the inverse square root of the atomic frame. The resulting
positive operator has rank at most `r`, operator norm at most
`1/lambda`, and trace equal to the sum of the squared block degrees.
Hence `dim_C(B)<=r/lambda`. Lift its finitely many matrix units
after discarding vanishing relative dimension, transport the exact
quadratic Kraus identities, and fill the complement by the identity
channel. The full maps converge uniformly in `infinity->2`, using
finite-head convergence and vanishing trace mass of the Kraus tails.

Finally, tracing finite-dimensional frame domination against the
minorant frame's support gives `lambda<=sqrt(r)||R_P||_HS`.
The artifact proves the canonical heat purity limit directly, so
the native exclusion requires no unproved rounding premise.
