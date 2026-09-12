---
rg: 2
id: injective-ca-random-order-transport-identity-proof
kind: route
title: Chain rule over the decoder memory plus left translation gives the random-order transport identity
target: injective-ca-random-order-transport-identity
requires: []
artifacts:
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---
Artifact Section 1, Theorem 1. Fix the order and list `N` increasingly. The chain rule gives
`sum_i I(x(e); y(n_i) | y(n_1), ..., y(n_(i-1))) = I(x(e); y(N)) = log |A|`, because `x(e)` is determined by `y(N)` and
the order is independent of `x`. Left translation by `n^-1` preserves the joint law of `(x, y, U)` and moves the
`n`-term to the output site `e`. The check on Z in Section 2.5 reproduces the value `2` bits.

**Verification.** `w4-vf-positive-b` passed this route in Section 5.1 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.
- **Re-derived:** both sides of the identity. The check on `Z` was recomputed on the input side and the output side.
- **Wording point:** for output alphabets `B != A`, domination under an amenable decoder memory group comes from counting inside
  `<N>`, not from the surjectivity theorem.
