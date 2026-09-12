---
rg: 2
id: amenable-coefficient-schur-kernel-proof
kind: route
title: Realize every multiplier of the coefficients by an embedded twisted regular representation
target: amenable-coefficients-have-zero-schur-kernel
requires: [schur-kernel-localizes-to-coefficient-subgroup, projective-unitary-classes-vanish-on-schur-kernel, kervaire-laudenbach-holds-for-hyperlinear]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S7 of the artifact.

1. `L(B)` embeds, so `B` is hyperlinear and injects into `B_w`.
   Localization reduces to `K_2(B, w) = 0`.
2. Each `gamma in Hom(H_2 B, U(1))` has a normalized cocycle `omega`.
   Embedding `L_omega(B)` in a tracial ultraproduct turns the twisted regular
   unitaries into a projective homomorphism with multiplier `gamma`.
3. The projective-multiplier theorem kills `gamma` on `K_2(B, w)`. `U(1)`
   separates the points of `H_2(B)`.

Amenable `B` has injective twisted algebras, which embed in `R^omega`.
