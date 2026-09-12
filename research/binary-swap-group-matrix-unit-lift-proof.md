---
rg: 2
id: binary-swap-group-matrix-unit-lift-proof
kind: route
title: Compute in the group algebra of the swap group S_3 and read the matrix block off the kernel idempotent
target: binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap
requires:
  - leavitt-evaluation-kernel-hits-augmentation-one
artifacts:
  - research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md
---

Artifact Section 1, Lemma 1.1 and Proposition 1.2.
- **Nilpotency:** Frobenius in `F_2[<u>]`.
- **Idempotency:** the explicit products in `F_2[S_3]`, with `g = uv`, `gv = u`, `g^2 v = w` and `wv = g^2`.
- **Images:** from `t_i s_j = delta_ij`.
- **Kernel idempotent:** `xy + yx = g + g^2 = 1 + z`, and the cited node gives `pi(z) = 0`.
