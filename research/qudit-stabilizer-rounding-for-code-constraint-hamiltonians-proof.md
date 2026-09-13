---
rg: 2
id: qudit-stabilizer-rounding-for-code-constraint-hamiltonians-proof
kind: route
title: Omega-commutation norm bound, pattern choice and centralizer averaging on prime qudits
target: qudit-stabilizer-rounding-for-code-constraint-hamiltonians
requires: []
artifacts:
  - research/artifacts/qudit-stabilizer-rounding-2026-09-12.md
---

Write `c_j g_j = |c_j| u_j`, let `psi` be a top eigenvector of `K`, put
`delta_j = 1-Re<psi|u_j|psi>`, `F = sum|c_j|delta_j = W-lambda_max`, and
`tau_d = sin^2(pi/d)/8`.

1. If `u_j u_k = omega^m u_k u_j` with `m != 0`, then `|1-omega^m| <= 2(sqrt(2delta_j)+sqrt(2delta_k))`,
   while `|1-omega^m| >= 2sin(pi/d)`. So `G = {delta_j < tau_d}` commutes.
2. Measure `{u_k : k in G}` jointly, and choose a positive-probability outcome `x`
   with `sum_(G*)|c_j|(1-Re x_j) <= sum_(G*)|c_j|delta_j`, where `G*` indexes the terms
   proportional to products of `G`.
3. `E_x != 0`, so `{x_k^(-1)u_k}` generates a scalar-free abelian Weyl group. For
   prime `d` it extends to maximal stabilizer groups; let `S_x` be their states,
   with `nu` uniform on `S_x`.
4. For `j not in G*`: a member of the group that fails to commute with `u_j` forces
   `<u_j>=0`. Otherwise the nondegenerate symplectic form on `C(A_x)/A_x` supplies a
   Weyl `R` in the centralizer with `R u_j = omega^m u_j R`, `m != 0`. `R` permutes
   `S_x`, so `E_nu<u_j> = 0`.
5. The average energy over `S_x` is at least `sum_(G*)|c_j|(1-delta_j)`, and the loss is at
   most `sum_(j not in G*)|c_j| max{0,1-delta_j} <= ((1-tau_d)/tau_d)F = (8/sin^2(pi/d)-1)F`.
6. For (CC_d): `Pi_S = |S|^(-1) sum_(g in S) g` has weight one, so
   `K = sum_a w_a Pi_(S_a)` has weight `W = sum_a w_a`, `H = WI-K`, and
   `<phi|H|phi> <= (1+C_d) lambda_min(H)`. Verification uses a `F_d` tableau;
   `<phi|Pi_S|phi>` is `|T|/|S|` or `0`, where `T` is the subgroup of `S` proportional to
   `Stab(phi)`. Mixed terms are bounded by `V`, as in the qubit proof.

Full proof in the linked artifact, Sections 2--3.
