---
rg: 2
id: odd-measure-kernel-haar-mass-proof
kind: route
title: Count weight-one odd vectors at each depth
target: odd-measure-kernel-carries-almost-all-haar-mass
requires: []
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

* **The pushforward.** Restriction to `P_n` maps `M_-` onto the odd vectors
  `O_n = {v in F_2^(P_n) : sum v = 1}`, which number `2^(2^n - 1)`. Haar measure pushes forward to
  the uniform measure on `O_n`.
* **Dirac measures.** A Dirac measure `delta_x` restricts to the indicator of the atom containing
  `x`, a vector of weight one. There are `2^n` such vectors, so
  `lambda(M_- \ U_n) = 2^n / 2^(2^n - 1)`.
* **Kernel.** `U_n` is clopen and avoids every Dirac measure, so `1_(U_n)` lies in the kernel
  (Theorem 2(4) of the artifact).
* **The intersection.** Suppose `mu` has weight one on every `P_n`. Additivity
  `mu(a) = mu(a0) + mu(a1)` places the level-`(n+1)` atom carrying the `1` inside the level-`n` one.
  The nested atoms define a point `x`, and `mu(C) = [x in C]` for every clopen `C`, so `mu = delta_x`.
  The measure of the complement tends to `0`.

Section 11 of the artifact.
