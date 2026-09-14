---
rg: 2
id: deligne-rank-collapse-via-sp4-schur-kernel
kind: route
title: A Schur-kernel certificate over Sp4(Z) kills the Deligne central mark in every rank model when the rank radical contains Schur kernels
target: deligne-central-mark-dies-in-char-p-rank-models
requires:
  - sp4-schur-kernel-meets-the-deligne-triple-class
  - schur-kernel-lies-in-char-p-linear-sofic-radical
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Artifact Corollary 3.5.
1. **Certificate.** `sp4-schur-kernel-meets-the-deligne-triple-class` gives a nonsingular `w` over `Sp_4(Z)` and a
   killed class `x` with `alpha_H(x) != 0` in `Z/3`.
2. **Radical.** For `p != 3` the center `C_3` has order prime to `p`, so the rank Schur radical theorem puts
   `alpha_H(x)` in `Rad_rk,p(E_3)`. It generates `C_3`, so `z in Rad_rk,p(E_3)`.
