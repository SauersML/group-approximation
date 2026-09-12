---
rg: 2
id: schur-kernel-localization-proof
kind: route
title: Read the Mayer--Vietoris sequence of the pushout amalgam at second homology
target: schur-kernel-localizes-to-coefficient-subgroup
requires: [kl-failure-localizes-to-the-coefficient-subgroup]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S6 of the artifact. The prerequisite gives
`Q_w = Q *_B B_w`, which is a genuine amalgam because `B` injects into
`B_w`. In `H_2(B) -> H_2(Q) (+) H_2(B_w) -> H_2(Q_w)`, a class `x` dies
exactly when `(x, 0)` is the image of some `y`, i.e. `x = iota_* y` with
`y` killed in `B_w`.
