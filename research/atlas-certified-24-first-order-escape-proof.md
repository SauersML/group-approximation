---
rg: 2
id: atlas-certified-24-first-order-escape-proof
kind: route
title: The certified-24 derivative kernel is computed and carries covariance energy six
target: atlas-certified-24-first-order-escape
requires: []
artifacts:
  - experiments/atlas_asc_tangent_exact.py
  - experiments/asc-exact-certified24.json
  - experiments/asc-exact-tangent5.json
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
---

Same reduction as
`atlas-boundary-tangent-covariance-coercivity-proof`: fold-triviality
telescopes each word's derivative into `rho(z_s)A`, so the 24 certified
representatives give the group-algebra element
`W_24 = sum_(s in S_24) z_s^* z_s` (support 93, trace 144, coefficient sum 0),
and the covariance element is `W_cov = 4 - 2 h_a - 2 h_b`.

Diagonalizing `lambda(W_24)` in the left regular representation gives rank
17802 and kernel dimension 2358, and the compression of `lambda(W_cov)` to
that kernel has operator norm `6.000000000009498`.  Since the kernel of a
sum of positive terms is the intersection of the individual kernels, any unit
vector realizing that norm is a first-order direction annihilating all 24
words while moving the covariances -- so the supremum defining the constant
is `+infinity` for this subset.

The contrast with the five-word screen is the content: adding words
`0, 11, 30, 44, 55` cuts the kernel from 2358 to 120 and the leak from 6 to
`2e-17`.
