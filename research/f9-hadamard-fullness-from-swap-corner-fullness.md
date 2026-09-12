---
rg: 2
id: f9-hadamard-fullness-from-swap-corner-fullness
kind: route
title: A swap corner solution conjugated by a constant F_9 unit solves the Hadamard spectral corner
target: f9-hadamard-spectral-idempotent-is-full
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

Corollary 1.4 of the artifact. Given `c e_- b = eps_-` in `S_-`, view it in `S_-^(9)`. With `f_+ = W e_- W^(-1)`,
`(c W^(-1)) f_+ (W b) = c e_- b = 1_-`.

This route and the chain `hadamard-spectral-fullness-gives-f9-cohn-family`,
`f9-cohn-family-descends-to-anti-central-summand`, `anti-central-cohn-family-gives-swap-corner-fullness` form an
intended equivalence cycle: the Hadamard spectral corner and the swap corner are the same problem. Neither
direction establishes either claim alone.
