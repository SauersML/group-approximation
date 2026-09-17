---
rg: 2
id: fpbs-simon-lieb-gauge-certificates-die-at-pc-proof
kind: route
title: Close the weighted Simon-Lieb recursion uniformly over roots, then pair u with its inverse
target: fpbs-simon-lieb-gauge-certificates-die-at-pc
requires: []
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

Complete proof in Sections 1–2 of the artifact. It uses only the definitions
and the independence of disjoint edge sets. No computation is used.

1. **(F2) Simon–Lieb.** Condition on the open cluster `C` of the root inside
   `U`. The last exit edge from `C` leaves `U`, and the remaining path avoids
   `C`. The three events are independent.
2. **Recursion.** For `F_n = max_{g in B_n} sum_{u in B_n} tau^{B_n}(g,u) w(g^{-1}u)`,
   apply (F2) with `Lambda = B_n` and `S' = gU ∩ B_n`. Boundary edges of `S'`
   inside `B_n` are translates of edges of `partial U`, and
   `tau^{S'} <= tau^{gU}`. Quasi-submultiplicativity gives
   `F_n <= C_U + K psi F_n`.
3. **Volume limit.** Monotone convergence gives a finite tilted sum.
4. **Pairing.** `w(u) w(u^{-1}) >= K^{-2}` and `tau(o,u) = tau(o,u^{-1})` give
   `chi_p <= K sum_u tau w`, so `theta(p) = 0` and `p <= p_c`.
5. **Strictness.** `psi` is a polynomial in `p`, so the certificate persists
   slightly above `p`.
6. **Envelope.** `w^#` is submultiplicative with `w^#(e) = 1`, and it is
   exactly the constant the recursion needs.
7. **Byproduct.** `chi_p < infinity` forces `phi_p(B_n) -> 0`, and the case
   `w = 1` then gives `p < p_c`.
