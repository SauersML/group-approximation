---
rg: 2
id: deligne-central-collapse-via-sp4-schur-kernel
kind: route
title: A Schur kill over Sp4(Z) detected mod three collapses the Deligne central mark
target: deligne-central-mark-hs-collapse
requires: [sp4-schur-kernel-meets-the-deligne-triple-class, schur-kernel-lies-in-hyperlinear-radical]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

The first prerequisite gives a class `x` in the Schur kernel with
`alpha_H(x) != 0` in `Z/3`. The second gives `alpha_H(x) in Rad_hyp(E_3)`,
and `alpha_H(x)` generates the center, so `z in Rad_hyp(E_3)`. `E_3` is
finitely presented, so a sequence of almost representations with vanishing
relator defect and `||phi_n(z) - I||_2 >= c > 0` would give, in the
ultraproduct, a homomorphism not killing `z`. That is (DCM1).
