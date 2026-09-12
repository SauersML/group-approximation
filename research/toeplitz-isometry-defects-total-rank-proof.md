---
rg: 2
id: toeplitz-isometry-defects-total-rank-proof
kind: route
title: Push through by block elimination, then write the partner isometry through the near-isometry
target: toeplitz-isometry-defects-have-total-rank-at-least-one
requires: []
artifacts:
  - research/artifacts/leavitt-ring-rank-approximability-collapse-2026-09-12.md
---

Section 1 of the artifact.

1. **Push-through (Lemma 1).** Block elimination gives
   `[[1,0],[-y,1]] [[1,x],[y,1]] [[1,-x],[0,1]] = diag(1, 1 - yx)` and
   `[[1,-x],[0,1]] [[1,x],[y,1]] [[1,0],[-y,1]] = diag(1 - xy, 1)`. So `rk(1 - xy) = rk(1 - yx)`.
   Orthogonal additivity (`rk(a + b) = rk a + rk b` for `a in eAe`, `b in (1-e)A(1-e)`, via
   `u = [e, 1-e]`) turns this into the corner form `rk(e - xy) = rk(e - yx)`.
2. **Annihilator bound (Lemma 2).** `X = X(e - ST) + (XS)T`, so `rk(X) <= rk(e - TS) + rk(XS)`.
3. **Toeplitz bound (Theorem 3).** Take `X = T_1`: then `rk(T_1) <= rk(e - T_0 S_0) + rk(T_1 S_0)`, and
   `rk(e) <= rk(T_1 S_1) + rk(e - T_1 S_1) <= rk(T_1) + rk(e - T_1 S_1)`.

The proof uses only three axioms: `rk(1) = 1`, `rk(MN) <= min(rk M, rk N)`, and additivity on block
diagonals. It uses no simplicity, no characteristic, and no ultraproduct.
