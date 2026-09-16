---
rg: 2
id: nonprime-minimal-lxi-counterexample-yields-loop-witness-proof
kind: route
title: Glue quotient paths along the pullback B = B_1 x_D B_2 after correcting their K1(SD) defect
target: nonprime-minimal-lxi-counterexample-yields-loop-witness
requires: []
artifacts:
  - research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md
---

The full proof is artifact `lxi-quotient-minimal-counterexamples-2026-09-16`: Section 0 facts (F1)--(F6),
Proposition 2(c), Theorem 3 and Corollary 4. The steps are:

0. **`D ≠ 0`.** If `J_1 + J_2 = B`, then because `J_1 ∩ J_2 = 0` we get `B ≅ B_1 ⊕ B_2`, and `J_1` is cut
   out by a central projection other than 0 and 1. Then quotient-minimality puts both components of `v` in
   the identity components, so `v ∈ U_0(B)`, which is a contradiction.
1. **Paths.** Quotient-minimality gives paths `h_i` in `U(B_i)` from 1 to `v_i = q_{J_i}(v)`. Also
   `[v] = 0` gives a path `Gamma` in `U(M_n(B))` from 1 to `diag(v, 1)`, with images `Gamma_i` in
   `M_n(B_i)` and a common image `Gamma_D` in `M_n(D)`.
2. **Bookkeeping.** Put `m_i = diag(h_i, 1) * Gamma_i̅`, a based loop in `U(M_n(B_i))`. Inserting the null
   backtrack `Gamma_D̅ * Gamma_D` gives
   `kappa_D(pi_1 h_1 * (pi_2 h_2)̅) = pi_{1*} kappa_{B_1}(m_1) − pi_{2*} kappa_{B_2}(m_2)`.
   This uses that `kappa` is a natural homomorphism on `pi_1` that is invariant under `diag(·, 1)`.
3. **Correction.** Each `B_i` is unital and properly infinite. By Bott periodicity
   `K_0(B_i) ≅ K_1(SB_i)`, `[e] ↦ kappa(t ↦ e^{2πit} e + 1 − e)`, and every `K_0` class is the class
   of a projection (BRR arXiv:0704.1554v1, Proposition 2.3(ii), due to Cuntz). So some based loop `mu_i`
   in `U(B_i)` has `kappa(mu_i) = −kappa(m_i)`. With `g_i = mu_i * h_i`, the loop
   `l = pi_1 g_1 * (pi_2 g_2)̅` has `kappa_D(l) = 0`.
4. **Reduction.** Suppose `[l] = [pi_1 lambda_1][pi_2 lambda_2]^{-1}` for loops `lambda_i` in `U(B_i)`.
   Replace `g_i` by `lambda_i̅ * g_i`. Then `pi_1 g_1` and `pi_2 g_2` are homotopic relative to endpoints
   via some `H: [0,1]^2 → U(D)`.
5. **Relative lifting.** Let `Y` be the union of the bottom and the two vertical edges of `X = [0,1]^2`.
   Put `G_Y = g_1` on the bottom edge, `1` on the left edge and `v_1` on the right edge. Consider the
   algebra `P = {(f, g) ∈ C(X, D) ⊕ C(Y, B_1) : f|_Y = pi_1 ∘ g}` and the map
   `Phi(k) = (pi_1 ∘ k, k|_Y)` from `C(X, B_1)`. `Phi` is surjective: take `g ∘ r` for a retraction
   `r: X → Y`, then add a lift of the remainder in `C_0(X \ Y, D)`. The path `(H ∘ rho_λ, G_Y)`, with
   `rho_λ` the straight-line homotopy from `id_X` to `r` rel `Y`, joins `(H, G_Y)` to `Phi(G_Y ∘ r)` in
   `U(P)`. So `U_0` lifting along `Phi` yields `G: X → U(B_1)` with `pi_1 ∘ G = H` and `G|_Y = G_Y`.
6. **Contradiction.** `G(·, 1)` is a path from 1 to `v_1` with `pi_1 G(·,1) = pi_2 g_2`. Since `J_1 ∩ J_2 = 0`,
   `B` is the pullback `B_1 ×_D B_2`, so the pair `(G(·,1), g_2)` is a path in `U(B)` from 1 to `v`, which is
   a contradiction. This proves item 2 of the claim, and constant `lambda_i` show `[l] ≠ 1`.
7. **Witness.** `C(T, D)` contains `D` unitally, so it is properly infinite. The injective unital map
   `(SD)~ → C(T, D)` sends `1 + (l − 1)` to `l`, so `[l]_{K_1(C(T,D))} = 0`. If `l ∈ U_0(C(T, D))`, then
   normalizing a free homotopy by its value at the base point gives a based null-homotopy, which contradicts
   item 2.

External inputs: Bott periodicity, cited from Rordam--Larsen--Laustsen, CUP 2000, Chapter 11, with the
theorem number not rechecked; and BRR Proposition 2.3(ii), read in the arXiv full text. Everything else is
proved in the artifact. Referee note (2026-09-16): the only consequence of Bott periodicity used in step 3 is
that every class in `K_1(SB_i)` is `kappa_{B_i}` of a based loop in `U(B_i)`. The artifact's (F5') proves
this directly for unital properly infinite algebras, using isometries with orthogonal ranges and a
Whitehead rotation, so step 3 does not depend on the unrechecked citation.
