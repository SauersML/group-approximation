---
rg: 2
id: spherical-artin-pbh-via-char-zero-linear-groups
kind: route
title: Spherical Artin groups are linear over Q(x,y), so the characteristic-zero permutational theorem puts them in B_A
target: spherical-artin-groups-satisfy-permutational-boone-higman
requires:
  - spherical-artin-groups-are-linear-over-q-x-y
  - char-zero-linear-groups-satisfy-permutational-boone-higman
---

Let `A(Γ)` be an Artin group of spherical type.

1. **Linearity.** By `spherical-artin-groups-are-linear-over-q-x-y`, `A(Γ)` is
   isomorphic to a subgroup `H <= GL_N(Q(x,y))`. `H` is finitely generated, since
   Artin groups are, and `Q(x,y)` has characteristic zero.
2. **Permutational form.** By
   `char-zero-linear-groups-satisfy-permutational-boone-higman`, `H` lies in
   `B_A`, and so does `A(Γ)`. ∎

Only transcendence degree 2 is used. The exceptional types need no separate
argument: the linearity import covers E_6, E_7 and E_8 directly, and F_4, H_3 and
H_4 through Crisp's embedding into products of A, D and E factors.
