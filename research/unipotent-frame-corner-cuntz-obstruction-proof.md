---
rg: 2
id: unipotent-frame-corner-cuntz-obstruction-proof
kind: route
title: A superdiagonal character of U_4(R) acting by translation gives nonzero defect, and directly finite corners carry no Toeplitz pair
target: unipotent-frame-relations-cannot-assemble-corner-cuntz-family
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - sofic-subgroups-carry-rank-models-violating-two-root-identity
artifacts:
  - research/artifacts/rank-four-plan-adversarial-audit-2026-09-12.md
---

Proof, artifact Section 1.

1. **The model.** For unitriangular matrices, `(gh)_(i,i+1) = g_(i,i+1) + h_(i,i+1)`, so
   `g |-> (g_12, g_23)` is a homomorphism `U_4(R) -> (R,+)^2`.
   - Take `phi : R -> F_p`, `F_p`-linear, with `phi(1) = 1`.
   - Let `C_p^2 = <u> x <v>` act on `F_p[C_p^2]` by translation.
   - Put `rho(g) = u^phi(g_12) v^phi(g_23)`.

   The higher roots and `x_34` map to `1`. With `x = u-1` and `y = v-1`, `N_23 N_12` is
   multiplication by `xy` on `F_p[x,y]/(x^p,y^p)`. Its image is spanned by `x^i y^j` with
   `1 <= i, j <= p-1`, so its rank is `(p-1)^2` of `p^2`.
2. **The relations.** `rho` is a homomorphism of `U_4(R)`, so it satisfies every relation among
   unitriangular elements. That includes all the isometry commutators and cross-frame readings of
   Plan 1, whose coefficients satisfy `t_i s_j = delta_ij` in `R`.
3. **No Toeplitz pair.** `T_0 S_0 = e` in the directly finite corner `eMe` gives `S_0 T_0 = e`,
   so `S_1 = S_0 T_0 S_1 = 0` whenever `T_0 S_1 = 0`.
4. **Consequences.**
   - The Weyl element `x_IJ(1) x_JI(-1) x_IJ(1)` conjugates `x_IJ(a)` to `x_JI(-a)`, so one
     opposite unit root element and `x_IJ(R)` generate `EL_2(R) = GL_2(R) ~= R^x`.
   - The regular sofic model of the nilpotent group `U_4(R)` gives the position-symmetric
     rank profile `1 - 1/p`, and in characteristic two `rk(N_23 N_12) = 3/8`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 3.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
