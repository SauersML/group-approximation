---
rg: 2
id: leavitt-matrix-units-lift-proof
kind: route
title: Cut the natural representation block of F_2[S_3] and read off matrix units
target: leavitt-matrix-units-lift-into-finite-subgroup-algebra
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

`F_2[S_3]` is the product of its principal block and the projective block of the
natural 2-dimensional representation `rho`. That block is `e F_2[H]`, with `e` the
central idempotent `1` plus the 3-cycle class sum, and `rho` maps it isomorphically onto
`M_2(F_2)`.

So `f_ij = x_ij e` with `rho(x_ij) = E_ij` is a matrix-unit system summing to `e`. Here
`x_11 = 1 + u + v + g`, `x_22 = u + v + g`, `x_12 = 1 + u`, `x_21 = 1 + v`. Multiplying
out with `ug = v`, `ug^2 = w`, `vg = w`, `vg^2 = u` gives the supports. Evaluation is
`Theta_2` of the natural representation, so `pi(f_ij) = s_i t_j`. (Artifact Lemma 5.)

*Verified independently by `gk-vf-linear` (2026-09-12): Section 16 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
