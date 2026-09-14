---
rg: 2
id: deligne-cover-rank-projective-approximation-proof
kind: route
title: Tensor rank projective models with regular representations of finite quotients, and cut extension models into a central eigenspace
target: deligne-cover-linear-soficity-is-rank-projective-approximation
requires:
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

Artifact Section 2.

- **2 => 1 (camouflage).** Put `sigma(s(g) z^i) = w^(ji) rho(g) (x) pi(g)`, where `pi` is the regular
  representation of a finite quotient of the residually finite `Gamma` that separates the ball.
  - The defect of `sigma` is the defect of `rho` tensored with a permutation matrix.
  - For `g != 1`, the kernel of `X (x) C_o - 1` has dimension at most `dim X`, so the separation is at least
    `1/2`.
  - For `g = 1`, `sigma(z^i)` is within rank `eps` of the scalar `w^(ji) != 1`.
- **1 => 2 (cutting).**
  - Round `sigma(z)` on `ker(sigma(z)^3 - 1)` to an exact order-three `Z`, within normalized rank `3 eps`.
  - Its eigenprojections `P_j` almost commute with the model, within `24 eps`.
  - Separation of `z` gives `r(P_1) + r(P_2) >= delta - 3 eps`.
  - Compressing to a heavy `P_j` gives `w^(ja)`-projective almost representations with defect `O(eps/delta)`,
    after a small-rank correction to invertibility.
  - A directedness argument fixes one `j` for all balls, and the contragredient `(rho^T)^(-1)` exchanges
    `j` and `3 - j`.

The cut needs `3` invertible in the field, which is why `p != 3`.
