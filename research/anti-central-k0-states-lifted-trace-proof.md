---
rg: 2
id: anti-central-k0-states-lifted-trace-proof
kind: route
title: Fourier inversion forces Haar measure on clopens, and essentially free orbit blocks force the lifted trace
target: anti-central-k0-states-equal-lifted-trace-on-signed-thompson
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

Section 2 of the artifact.
- **Part 1:** the half split `s(Q_C) = 1/2` from `tau_(X\C) = z tau_C` and transitivity of `V` on proper clopens, then
  Fourier inversion on the atoms of a prefix code.
- **Part 2:** enlarge `K` to `E^(m) x| F`, whose anti-central algebra is `C(O_m, F_3) x| F`. On free orbit blocks
  `M_|F|(F_3)` both the state and the lifted trace are rank times `lambda` of a point atom. Non-free orbits carry
  Haar mass at most `sum_(g != 1) 2^(1 - 2^(m - |alpha_g|))`, which tends to zero.
