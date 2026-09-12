---
rg: 2
id: measurable-certificate-routing-preserves-bernoulli-proof
kind: route
title: Transport incoming reads, flip an unread coordinate, and force in-degree one
target: measurable-certificate-routing-preserves-bernoulli-measure
requires: []
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Section 2 of the artifact.

1. **Transport.** Equivariance gives `rho_c(g) = 1` exactly when `rho_(g^-1.c)(1) = g^-1`. Shift
   invariance of `mu_C` then gives `E #rho_c^-1(1) = sum_g mu_C{ rho_c(1) = g^-1 } = 1`.
2. **Every site is read.** Let `tau` be injective on the conull set `X_0`. For almost every `c` the
   section `X_0^c` is `mu_D`-conull. Suppose some `h` is outside the image of `rho_c`. Applying a
   fixed-point-free permutation of `D` at coordinate `h` is a measure-preserving bijection of `D^G`.
   On the conull set `X_0^c ∩ flip^-1(X_0^c)` it changes `d` without changing `tau(c, d)`,
   contradicting injectivity.
3. **In-degree one.** The in-degree at `1` is almost surely at least `1` and has mean `1`, so it is
   almost surely `1`. Equivariance and countability give in-degree one at every site for almost every
   `c`, so `rho_c` is bijective.
4. **Measure.** For such `c`, `d -> y` permutes coordinates and symbols, so it preserves `mu_D`.
   Fubini gives `tau_* mu = mu`.
