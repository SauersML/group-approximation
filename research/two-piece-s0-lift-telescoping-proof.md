---
rg: 2
id: two-piece-s0-lift-telescoping-proof
kind: route
title: Factor the product into a square-zero unit times a Peirce-triangular element, then read off the Schur complement
target: two-piece-s0-lifts-telescope-to-a-corner
requires: []
artifacts:
  - research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md
---

Artifact Section 2: Lemma 2.1, Theorem 2.2, Corollary 2.3, Proposition 2.4 and Remark 2.5.
- **Factorization.** `1 + X + Y = (1+Y)(1 + X + YX)`, because `Y^2 = 0`.
- **Triangular form.** The second factor is `[[E^, X],[0, C'C]]` in Peirce form. It is invertible exactly when
  `C'C` is invertible in the corner. The converse direction reads the Peirce blocks of an inverse.
- **Nilpotency.** `(X+Y)^2 = XY + YX`, and `XY` and `YX` lie in orthogonal corners.
- **Corner reading.** `pi(X) = pi(Y) = 0`, and `g1^(-1) P_0 g1 = P_0 + g1^(-1) P_01 g1`.
