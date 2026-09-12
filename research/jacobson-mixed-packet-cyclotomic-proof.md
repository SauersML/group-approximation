---
rg: 2
id: jacobson-mixed-packet-cyclotomic-proof
kind: route
title: Build two integer reflection blocks on a cyclotomic packet and certify nonzero determinants
target: jacobson-mixed-packet-attains-rank-eight-below-two
requires: []
artifacts:
  - research/artifacts/jacobson-mixed-packet-certificate-2026-09-07.md
  - experiments/jacobson_mixed_cyclotomic_certificate.py
  - research/artifacts/jacobson-mixed-cyclotomic-replay-2026-09-07.json
---

The artifact gives all data and the finite-certificate proof. Exact
verification of all 336 generator edges constructs the unitary
`GL_3(F_2)` representation. Its finite-overlap sign projection and two
displayed integer involutions construct `H`. The two nonzero
cyclotomic determinants exclude the eigenvalue minus one from the
braid cubes, proving strict operator-norm defects below two. The marked
trace is exactly minus four in dimension twelve, so the marked negative
rank is eight. No floating-point search or Kazhdan input enters the
certificate.
