---
rg: 2
id: deligne-opnorm-sectors-empty-via-sp4-schur-kernel
kind: route
title: A Schur kill over Sp4(Z) detected mod three excludes both operator-norm Maslov sectors
target: deligne-nontrivial-maslov-opnorm-sectors-are-empty
requires: [sp4-schur-kernel-meets-the-deligne-triple-class, projective-unitary-classes-vanish-on-schur-kernel]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S9 of the artifact. A point-norm model in the `alpha` or `alpha^2`
sector is an exact projective homomorphism into the unitary group of a norm
matrix corona modulo scalars, with that multiplier. The second prerequisite,
with `N = N_op`, kills its evaluation on the Schur kernel. The first
prerequisite supplies a killed `x` with `alpha_H(x) != 0` in `Z/3`, and so
`2 alpha_H(x) != 0` as well. Contradiction.
