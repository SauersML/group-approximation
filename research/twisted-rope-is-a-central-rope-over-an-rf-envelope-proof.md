---
rg: 2
id: twisted-rope-is-a-central-rope-over-an-rf-envelope-proof
kind: route
title: Extend the fold to all of Gamma_e, realize the twist in a finite-quotient-compatible HNN, then substitute the conjugator
target: twisted-rope-is-a-central-rope-over-an-rf-envelope
requires:
  - mf-safe-finite-presentation-compiler
  - three-bridge-is-cyclic-fiber-product-with-finite-cep
  - asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope
  - centralizer-hnn-is-free-generalized-wreath
  - gkp-free-generalized-wreath-soficity
artifacts:
  - research/artifacts/twisted-rope-rf-envelope-2026-09-13.md
---

Full derivation: `research/artifacts/twisted-rope-rf-envelope-2026-09-13.md`,
Sections 1--4.

1. **(L1).** `Lambda` is a product of homomorphisms on `K_e`. It sends `L_e^0`
   to `1` and `(f, q_+(f)) in L^g` to the diagonal `(q_+(f), q_+(f))`, which
   `sigma` centralizes. So the relators `[v,l]` hold. Since `F` sits in `K_e`
   as `f |-> (i_e(f), (f,1))`, `Lambda(f) = (q_+(f), 1)` and
   `Lambda(vfv^-1) = (1, q_+(f))`. So `tau_e` and `pr_1 o Lambda` are two
   homomorphisms `S_e -> H` that agree on `F u F^v`. On `INF`, `q_e = q_+`.
2. **(E1).** For a finite quotient `r : P -> C`, the map
   `((p_1,p_2)sigma^eps, q) |-> ((r p_1, r p_2)sigma^eps, r q)` carries the
   associated subgroups onto `(r H x r H) x 1` and `{(c, pr_1 c)}`
   compatibly, so it induces a map from `R-hat` to an HNN extension of a
   finite group, which is virtually free. Given a Britton-reduced word, take
   `r = (r', chi mod m)`, with `m` dividing no nonzero `chi(p_j)` and `r'`
   separating the finitely many `q` and `q p_1^-1` involved. Then
   `r(H) <= C' x 0` keeps every letter outside the image edges. The image word
   is Britton-reduced, hence nontrivial.
3. **(E2)--(E3).** `Lambda(g')` commutes with `q` in `G-hat x H`, so `iota` is
   a homomorphism. It is injective coordinatewise. For `s in S_e`,
   `(1,w)(s,(Lambda s,1))(1,w)^-1 = (s,(Lambda s, pr_1 Lambda s)) = iota(s, tau_e s)`
   by (L1).
4. **(E4).** This is (IE1) of
   [[asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope]], with base
   `iota(Gamma_e x H)`, overgroup `D_e`, and inner conjugator `(1,w)`.
5. **(E5).** This is (CGW1) of [[centralizer-hnn-is-free-generalized-wreath]],
   for the inclusion `C_e <= D_e`.
6. **(E6).** `D_e` is sofic when `Gamma_e` is, since `R-hat` is residually
   finite and direct products of sofic groups are sofic. GKP Theorem 3.7
   ([[gkp-free-generalized-wreath-soficity]]) makes `Omega_e` sofic once the
   coset action is sofic. Soficity passes to the subgroup `R_e`.
