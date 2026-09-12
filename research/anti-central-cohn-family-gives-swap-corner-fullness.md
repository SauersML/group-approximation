---
rg: 2
id: anti-central-cohn-family-gives-swap-corner-fullness
kind: route
title: Transport a Cohn family of the summand into the swap corner by the diagonal endomorphism
target: ternary-anti-invariant-swap-corner-is-full
requires:
  - ternary-anti-central-summand-has-cohn-family
  - anti-central-ternary-summand-contains-its-matrix-ring
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

Theorem 2.1, (b) implies (a), of the artifact. Given `tau_i sigma_j = delta_ij 1_-` in `S_-`, put

```text
b = e_- delta_*(sigma_1) + e_- [d] delta_*(sigma_2),
c = e_- delta_*(tau_1)   + [d] e_- delta_*(tau_2).
```

`delta_*(S_-)` commutes with `e_-` and `[d]`, and `e_- [d] e_- = 0`, `[d] e_- [d] = 1_- - e_-`. So
`c e_- b = e_- + 0 + 0 + (1_- - e_-) = 1_-`.

This route and `swap-corner-fullness-gives-anti-central-cohn-family` form an intended two-route
cycle: the two claims are equivalent. Neither route can establish either claim alone.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 15 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
