---
rg: 2
id: c-tilde-artin-pbh-via-braid-group-embedding-proof
kind: route
title: Embed the twice-punctured plane braid group in B_(n+2) by the Fadell--Neuwirth fibration and inherit PBH from Aut(F_(n+2))
target: c-tilde-artin-groups-satisfy-permutational-boone-higman
requires:
  - c-tilde-artin-groups-are-punctured-plane-braid-groups
  - aut-free-groups-satisfy-permutational-boone-higman
  - type-a-action-gives-boone-higman-for-subgroups
---

Fix `n >= 1`, and let `P = C - {p, q}` with `p ≠ q`.

**1. Identification.**
- For `n >= 2`, `A(C̃_n) ≅ π_1 UConf_n(P)` by
  `c-tilde-artin-groups-are-punctured-plane-braid-groups`.
- For `n = 1`, the diagram C̃_1 has two nodes joined by an edge labelled `∞`.
  So `A(C̃_1)` is free of rank 2, which is `π_1(P) = π_1 UConf_1(P)`.

**2. The fibration.** Let `Conf_m(C)` be the ordered configuration space.
1. **Local triviality.** By Fadell--Neuwirth, the projection
   `π : Conf_(n+2)(C) -> Conf_2(C)`, `(z_1, ..., z_(n+2)) |-> (z_1, z_2)`, is a
   locally trivial bundle with fibre `Conf_n(C - {z_1, z_2})`. Over a small ball
   `U` around `(p,q)` choose homeomorphisms `h_b` of `C`, continuous in `b ∈ U`,
   with `h_b(p) = b_1`, `h_b(q) = b_2`, and `h_(p,q) = id`. The trivialization
   `U × Conf_n(P) -> π^-1(U)` sends `(b, w_1, ..., w_n)` to
   `(b_1, b_2, h_b(w_1), ..., h_b(w_n))`.
2. **Quotient by S_n.** The group `S_n` permutes the last `n` coordinates. It
   acts freely on `Conf_(n+2)(C)`, preserves the fibres of `π`, and commutes with
   the trivializations. So `E = Conf_(n+2)(C)/S_n` fibres over `Conf_2(C)` with
   fibre `UConf_n(P)`.
3. **Injectivity.** `Conf_2(C) ≅ C × C^×` is aspherical, so `π_2(Conf_2(C)) = 0`.
   The fibre is connected, so the homotopy exact sequence gives an injection
   `π_1 UConf_n(P) -> π_1(E)`.
4. **Into B_(n+2).** `E` is connected. The map `E -> UConf_(n+2)(C)` that forgets
   which two points are labelled is a covering of degree `(n+2)(n+1)`. So
   `π_1(E)` is a subgroup of index `(n+2)(n+1)` in `B_(n+2) = π_1 UConf_(n+2)(C)`.

Hence `A(C̃_n)` embeds in `B_(n+2)`. Charney--Crisp, arXiv:math/0408412v1, p. 2,
state the same embedding: A(C̃_(n−1)) is the subgroup of A(A_n) = B_(n+1)
fixing two punctures. The derivation above only re-checks it.

**3. Permutational Boone--Higman.** In the proof of their Corollary B, BFFHZ put
braid groups inside `Aut(F_m)` through `B_m -> LB_m -> LB^ext_m -> Aut(F_m)`.
`Aut(F_m)` satisfies the permutational property
(`aut-free-groups-satisfy-permutational-boone-higman`). That property asks for
an embedding in some group with a type (A) action, so it passes to subgroups.
Therefore `B_(n+2)` has it, and so does `A(C̃_n)`.

**4. A finitely presented simple envelope.** By
`type-a-action-gives-boone-higman-for-subgroups` (Zaremsky, arXiv:2405.18354,
Corollary B), every subgroup of a group with a type (A) action embeds in a
finitely presented simple group. So `A(C̃_n)` embeds in one. QED
