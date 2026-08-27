---
rg: 2
id: atlas-square-root-bridge-two-matrix-proof
kind: route
title: Amplify the two-matrix residual polynomials and telescope across the outer-product bridge
target: atlas-square-root-bridge-two-matrix-rank-reduction
requires:
  - atlas-q14-growing-width-rank-one-bridge-is-sharp
  - atlas-morita-coefficient-cyclicity-reduction
---

At the unbridged chart, every fixed packet or collision word evaluates to
its two-matrix polynomial tensored with `I_k`, so rank multiplies by `k`.
The bridge changes the chart and inverse by rank one.  Each second-chart
syllable consequently changes by rank at most two, and telescoping a fixed
word costs at most twice its number of second-chart syllables.  The bridge
simultaneously makes the coefficient algebra full, turning any surviving
nonzero residual image into a cyclic seed.
