---
rg: 2
id: iwahori-eisenstein-angle-proof
kind: route
title: Complementary ramification weights make the Gram matrix five minus twice a degree-two incidence
target: iwahori-eisenstein-angle
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - experiments/iwahori_eisenstein_angle.py
---

Model cusps of `B(p)` as (cusp of `Gamma(p)`, numerator parity); the two
restrictions have ramification weights `e_1` and `3 - e_1`; the Gram
matrix of the mismatch map is `5I - 2[[0,A],[A^T,0]]` with `A` a `0/1`
incidence of row and column sums `2`; Schur's test bounds `||A|| <= 2`.
Verified numerically for all primes up to `101` (exact values `1` and `3`).
