---
rg: 2
id: swap-corner-fullness-gives-anti-central-cohn-family
kind: route
title: Square the corner's Cohn family and place it on the diagonal of the summand's matrix picture
target: ternary-anti-central-summand-has-cohn-family
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

Theorem 2.1, (a) implies (b), of the artifact.

1. From `c e_- b = 1_-`, the elements `beta_j = e_- b [d]^(j-1) e_-` and
   `gamma_i = e_- [d]^(i-1) c e_-` form a Cohn family in the corner `T = e_- S_- e_-`.
2. The four products `beta_i beta_j` and `gamma_j gamma_i` form a four-pair Cohn family in `T`.
3. The diagonal elements `v_1 + [d] v_2 [d]` and so on, in the matrix picture `S_- ~= M_2(T)` of part
   2 of `ternary-leavitt-swap-problem-splits-at-central-involution`, give
   `tau_a sigma_b = delta_ab 1_-`. Every cross term `x [d] y` with `x, y` in `T` vanishes.

Intended two-route cycle with `anti-central-cohn-family-gives-swap-corner-fullness`: the claims are
equivalent.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 15 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
