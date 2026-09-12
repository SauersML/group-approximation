---
rg: 2
id: block-unipotent-rank-models-of-leavitt-el3-proof
kind: route
title: Steinberg triples build matrix units and a unital corner homomorphism, which direct finiteness of the corner kills
target: block-unipotent-rank-models-of-leavitt-el3-are-trivial
requires: []
artifacts:
  - research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md
---

Section 5 of the artifact. Indices `i, j, k` are always distinct. The ring facts used are
that `L_K(1,n)`, `n >= 2`, is simple and satisfies `t_0 s_0 = 1 != s_0 t_0` (Leavitt 1962;
for `K = F_2` and `n = 2` the identity is `binary-leavitt-algebra-not-directly-finite`).

1. **Block calculus.** For `X in e_i M e_j` and `Y in e_j M e_k`, `X^2 = Y^2 = YX = 0`, so
   `(1 + X)^(-1) = 1 - X` and `[1 + X, 1 + Y] = 1 + XY`: every other monomial of the
   expansion contains `YX`, `X^2` or `Y^2`. For `X, X'` in `e_i M e_j`, `X X' = 0`. So the
   Steinberg relations give (A) additivity of each `psi_ij` and (B)
   `psi_ij(a) psi_jk(b) = psi_ik(ab)`. The relations `[x_ij(a), x_kl(b)] = 1` with
   `j != k`, `i != l` hold automatically.
2. **Matrix units.** `u_ij = psi_ij(1)` satisfy `u_ij u_jk = u_ik`. With
   `{i, j, k} = {1, 2, 3}`, `u_ji = u_jk u_ki` gives `u_ij u_ji = u_ik u_ki`, so
   `p_i = u_ij u_ji` does not depend on `j`. Then `p_i u_ij = u_ik u_ki u_ij = u_ik u_kj = u_ij`
   and `u_ij p_j = u_ij u_jk u_kj = u_ij`. Hence `p_i^2 = u_ij p_j u_ji = p_i`, and `u_ij`,
   `u_ji` are mutually inverse between the corners: `u_ij u_ji = p_i`, `u_ji u_ij = p_j`.
   In a rank ultraproduct `rk(p_1) = rk(p_2) = rk(p_3)`.
3. **Support.** `psi_ij(a) = psi_ik(a) u_kj = psi_ij(a) p_j` and
   `psi_ij(a) = u_ik psi_kj(a) = p_i psi_ij(a)`.
4. **Corner homomorphism.** `phi(a) = psi_12(a) u_21`, which equals
   `psi_13(a) u_32 u_21 = psi_13(a) u_31`. It is additive by (A), lies in `p_1 M p_1` by
   steps 2 and 3, has `phi(1) = p_1`, and is multiplicative:
   `phi(a) phi(b) = psi_12(a) u_21 psi_13(b) u_31 = psi_12(a) psi_23(b) u_31 = psi_13(ab) u_31 = phi(ab)`.
   Moreover `psi_ij(a) = u_i1 phi(a) u_1j`, with `u_11 = p_1`, so `phi` determines every
   `psi_ij`.
5. **Direct finiteness.** A corner of a directly finite ring is directly finite: if
   `ab = p` with `a, b in pMp`, then `(a + 1 - p)(b + 1 - p) = 1`, so
   `(b + 1 - p)(a + 1 - p) = 1` and `ba = p`. From `phi(t_0) phi(s_0) = p_1` we get
   `phi(s_0 t_0 - 1) = 0`. If `p_1 != 0`, `ker phi` is a proper two-sided ideal of the
   simple ring `R_K`, so `phi` is injective, contradicting `s_0 t_0 != 1`. Hence
   `p_1 = 0`, so `phi = 0`, and every `psi_ij = u_i1 phi u_1j = 0`.
6. **Weyl elements.** By (A) `psi_ji(-1) = -u_ji`, and
   `sigma(w_ij) = (1 + u_ij)(1 - u_ji)(1 + u_ij) = (1 - p_i - p_j) + u_ij - u_ji`, using
   `u_ij u_ji u_ij = u_ij`. Only `rk(p_i) = rk(p_j)` is forced; `e_i - p_i` is acted on
   trivially.
7. **Finite stages.** Approximate block support and asymptotic multiplicativity become
   exact in the rank ultraproduct, so every element is sent to `1` there, i.e.
   `rk(sigma_k(g) - 1) = o(N_k)`.
