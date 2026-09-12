---
rg: 2
id: formalizability-conormal-jacobian-cokernel-proof
kind: route
title: Compute the free conormal module by de Rham and read the encoder lift as the reduced Jacobian
target: formalizability-conormal-obstruction-is-jacobian-cokernel
requires: []
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
---

Section 3 of the artifact.

1. **`Omega_B = 0`.** `B` is Boolean, so `y = y^2` for every `y`. In characteristic
   `2`, `dy = d(y^2) = 2y dy = 0`, so `Omega_{B/F_2} = 0`.
2. **Free conormal module.** The cotangent sequence of `R -> R/I = B` is
   `I/I^2 --d--> Omega_R (x)_R B -> Omega_B -> 0`. With `Omega_B = 0`, `d` is onto the
   free `B`-module `(+)_h B dX_h`. On generators `d(u_h) = (2X_h + 1) dX_h = dX_h`,
   which are a free basis, so `d` is an isomorphism and `I/I^2` is free on `{u_h}`.
3. **Encoder lift is the Jacobian.** `hat tau^*(u_h) = hat mu_h^2 + hat mu_h`; apply
   `d`: `d(hat mu_h^2 + hat mu_h) = (2 hat mu_h + 1) d hat mu_h = d hat mu_h =
   sum_{h'} (partial hat mu_h/partial X_{h'}) dX_{h'}`, coefficients reduced mod `I`.
   Transporting by `d^{-1}` gives the matrix `J_B` in the `{u_h}` basis.
4. **Constant slice.** Evaluating the Boolean coefficients at a constant
   configuration `c` and using equivariance gives
   `J_tau(c) = sum_m (partial mu/partial X_m)(c) delta_m in M_n(F_2[G])`, the Theorem 1
   linearization. Its cokernel over `F_2[G]` is the constant slice of
   `coker(J_B)`, and vanishes iff `J_tau(c)` is a split epimorphism.

The route proves the three structural facts. It does not compute the higher-layer
cokernels and does not decide formalizability.
