---
rg: 2
id: sylvester-commuting-compression-proof
kind: route
title: Check the Sylvester axioms after multiplying by the commuting element, and run the rank calculus through block row and column operations
target: sylvester-rank-functions-compress-along-commuting-elements
requires: []
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

Artifact Section 1.

1. **Compression.**
   * Normalization and zero are immediate.
   * `N(X'Y'P) <= N(Y'P)`. Since `P` commutes with the entries of `Y'`, `X'Y'P = X'PY'`, so
     `N(X'Y'P) <= N(X'P)`.
   * Multiplying by the scalar matrix `P` preserves direct sums and upper triangular blocks entrywise.
2. **Commuting idempotents.** With `U = [[e, 1-e],[1-e, e]]` and `U^2 = 1`, invertible row and column
   operations carry `diag(eP, (1-e)P)` to `diag(P, 0)`, using `eP = Pe`.
3. **Frobenius.** `[[XY, 0],[Y, YZ]]` is triangular after a permutation, so its rank is at least
   `N(XY) + N(YZ)`. Invertible operations carry it to `[[0, -XYZ],[Y, 0]]`, whose rank is `N(Y) + N(XYZ)`.
4. **Commuting nilpotents.** Put `a_j = N(x^j P)`. Frobenius applied to `(x, x^j P, x)` gives
   `2 a_(j+1) <= a_j + a_(j+2)`, so `a` is convex with `a_m = 0`, and `a_1 <= (1 - 1/m) a_0`. QED

*Verified independently by `w4-vf-gate` (2026-09-12), Section 23.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
