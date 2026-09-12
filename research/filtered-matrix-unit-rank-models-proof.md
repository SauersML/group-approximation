---
rg: 2
id: filtered-matrix-unit-rank-models-proof
kind: route
title: Kill each graded piece by the matrix-unit theorems, transposed pieces through the opposite ring, then glue by perfection
target: filtered-matrix-unit-rank-models-of-simple-el3-are-trivial
requires:
  - perfect-groups-have-no-triangular-models-with-trivial-diagonal
  - matrix-unit-root-rank-models-of-simple-el3-are-trivial
  - matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Artifact Section 2, Theorem 2.

1. **Corners.** Each graded piece is a homomorphism into the units of the corner
   `h_t M h_t`. Lifting `h_t` to idempotents at finite stages shows the corner is again a rank
   ultraproduct over characteristic `p`, or zero.
2. **Matrix-unit pieces** are trivial by the two matrix-unit corollaries: characteristic two,
   and odd characteristic.
3. **Transposed pieces.** `R^op` is simple and not directly finite, so the same corollaries
   for `EL_3(R^op)` make `sigma_t o theta^-1` trivial.
4. **Trivial pieces** need nothing.
5. **Gluing.** `EL_3(R)` is perfect, because `x_ik(a) = [x_ij(a), x_jk(1)]`. Every graded piece
   is trivial, so `perfect-groups-have-no-triangular-models-with-trivial-diagonal` makes
   `sigma` trivial.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 32 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
