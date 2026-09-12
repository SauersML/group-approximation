---
rg: 2
id: schur-kernel-hyperlinear-radical-proof
kind: route
title: Cut a tracial model down to a central character and compare projective multipliers
target: schur-kernel-lies-in-hyperlinear-radical
requires: [projective-unitary-classes-vanish-on-schur-kernel]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S4 of the artifact. Suppose `psi : E -> U(M)`, with `M` a tracial
ultraproduct of matrix algebras, does not kill `z_0 = alpha_H(x)` for some
killed class `x`.

1. Joint spectral projections of finitely many `psi(z_i)` commute with
   `psi(E)` and give corner homomorphisms on which `psi(Z)` is scalar up to
   `1/k` in operator norm, with `psi(z_0)` near a fixed `lambda != 1`.
2. The ultraproduct over `k` of these corners is an exact homomorphism
   `psi_inf` into another algebraic unitary quotient, with
   `psi_inf(z) = chi(z) 1` for a character `chi` and `chi(z_0) = lambda`.
3. `psi_inf` is a morphism of central extensions, so the induced projective
   homomorphism of `Q` has multiplier `chi o alpha_H`. The prerequisite kills
   it on `x`, so `chi(z_0) = 1`, a contradiction.
