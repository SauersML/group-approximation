---
rg: 2
id: el3-two-root-identities-matrix-units-proof
kind: route
title: Squares and reversed composable products vanish, so commutators become products and N_ij N_ji are orthogonal idempotents
target: el3-unit-root-matrix-units-iff-two-root-identities
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Complete proof: artifact Section 1.

- **Matrix units give the identities.** Matrix units lie in the corners `p_a M p_b`, and the
  corners are orthogonal.
- **The identities give matrix units.**
  - With `X = N_ij`, `Y = N_jk`, `X^2 = Y^2 = YX = 0`, the commutator
    `[1+X, 1+Y] = (1+X)(1+Y)(1-X)(1-Y)` expands to `1 + XY`. So `N_ik = N_ij N_jk`.
  - Hence `p_i = N_ij N_ji` is idempotent, independent of `j`, and satisfies
    `p_i N_ij = N_ij = N_ij p_j`. Also `p_i p_j = N_ij N_ji^2 N_ij = 0`.
- **Weyl symmetry.** Signed permutation matrices permute the roots, and `N_x(-1)` equals `N_x`
  times a unit commuting with `N_x`. So the ordered pairs `(ab, cd)` with `b != c` reduce to
  four orbits, and the proof uses only the squares and the reversed-composable orbit
  `N_23 N_12`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 35 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
