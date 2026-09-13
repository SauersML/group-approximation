---
rg: 2
id: pmf-permanence-amenable-kernel-without-exactness-proof
kind: route
title: Tensor the finite affine permutation actions with the quotient's representations; the n-limit is an induced representation from the amenable kernel
target: pmf-permanence-amenable-kernel-without-exactness
requires: []
artifacts:
  - research/artifacts/sl3z-pmf-affine-reformulation-2026-09-13.md
---

Complete proof in the artifact, Section 1, steps 0--6.

1. Strong convergence gives an isometric `C*_r(Q) -> prod M_(k_n) / sum M_(k_n)`.
   Tensoring with `M_d` keeps it isometric, so strong convergence holds for
   matrix coefficients.
2. `rho_(N,n) = pi_N (x) (sigma_n o p)` evaluated on `z` is
   `(id (x) sigma_n)(x_(N,z))`, with `x_(N,z)` in `M_(|A/A_N|)(C[Q])`.  So the
   `n`-limit of the norm is the norm under
   `rho_(N,inf) = pi_N (x) Ind_A^G 1 = Ind_A^G (pi_N|_A)`.
3. `pi_N|_A` is the quasi-regular representation on `A/A_N`.  It is weakly
   contained in `lambda_A`, because `A` is amenable.  Induction gives
   `||rho_(N,inf)(z)|| <= ||lambda_G(z)||`.
4. `pi_N <= pi_(N')` for `N <= N'`, and `1_(A_N) -> delta_e` pointwise.  So
   `lambda_A` is weakly contained in `(+)_N pi_N|_A`, and after induction
   `sup_N ||rho_(N,inf)(z)|| = ||lambda_G(z)||`.
5. Take a diagonal sequence over an `l^1`-dense sequence of group-ring elements.

The only coefficient algebra is finite-dimensional, so exactness is never used.
Model test: for `A = F_2` (not amenable) step 3 fails, since `l^2(F_2/A_N)`
contains the trivial representation.
