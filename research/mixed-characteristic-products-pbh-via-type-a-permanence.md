---
rg: 2
id: mixed-characteristic-products-pbh-via-type-a-permanence
kind: route
title: Put each factor in its own type (A) actor and use closure of the permutational class under finite direct products and finite-index overgroups
target: mixed-characteristic-linear-products-satisfy-pbh
requires:
  - char-zero-linear-groups-satisfy-permutational-boone-higman
  - char-two-curve-linear-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Let `B_A` be the class of groups embedding in a group with an action of type (A)
(`boone-higman-type-a-class-closed-under-finite-extensions`).

1. `G_0 ∈ B_A` by `char-zero-linear-groups-satisfy-permutational-boone-higman`.
2. `G_2 ∈ B_A` by item 1 of `char-two-curve-linear-groups-satisfy-permutational-boone-higman`.
3. By item 1 of `boone-higman-type-a-class-closed-under-finite-extensions`, `B_A` is closed under
   subgroups and finite direct products, so `G_0 × G_2 ∈ B_A`. By item 2 there, `B_A` is closed
   under finite-index overgroups.
4. By item 3 there, every group in `B_A` embeds in a finitely presented simple group. ∎
