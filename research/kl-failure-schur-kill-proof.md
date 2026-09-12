---
rg: 2
id: kl-failure-schur-kill-proof
kind: route
title: Amalgamate a torus along the killed coefficient and read Mayer--Vietoris
target: kl-failure-yields-a-schur-kill
requires: []
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S8 of the artifact. `<a>` is cyclic, so `H_2(<a>) = 0`, and the
Mayer--Vietoris sequence of the amalgam injects
`H_2(<a> x Z) = H_1(<a>) (x) Z != 0` into `H_2(Q)`. The map
`<a> x Z -> Q_w` kills `a`, so it factors through `Z`, and `H_2(Z) = 0`.
