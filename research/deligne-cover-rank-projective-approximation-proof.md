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

*Verification by `w4-vf-linear-b` (2026-09-12), Section 22 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md` (8987f4ea69): PASS, every constant re-derived.*
- *Camouflage defect. Kernel of `X tensor C_o - 1` has dimension at most `d` even when `p | o`, and `r(σ(z^i) - 1) >= 1 - ε`.*
- *Rounding. `M^3 - 1` gives `3ε`, and the commutator bounds are `8ε`, `16ε` and `24ε`.*
- *Heavy sector `r(P_j) >= (δ - 3ε)/2`, compression count `33ε`, invertibility repair `135ε`.*
- *Directedness fixes one `j`, and the contragredient symmetry exchanges `j` and `3 - j`.*
- *Corollary 2.5. An `F_p` rank model is an `F`-model for every `F` of characteristic `p`, because rank is unchanged under extension of scalars. The established `linear-sofic-group-algebra-is-stably-finite` then applies.*
