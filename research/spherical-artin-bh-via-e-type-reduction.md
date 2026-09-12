---
rg: 2
id: spherical-artin-bh-via-e-type-reduction
kind: route
title: Permutational Boone--Higman for E_6, E_7, E_8 gives simple envelopes for every spherical Artin group
target: spherical-artin-groups-satisfy-boone-higman
requires:
  - spherical-artin-boone-higman-reduces-to-e6-e7-e8
  - e-type-artin-groups-satisfy-permutational-boone-higman
  - type-a-action-gives-boone-higman-for-subgroups
---

Let `A(Γ)` be of spherical type.

1. **The E types.** By `e-type-artin-groups-satisfy-permutational-boone-higman`,
   `A(E_6)`, `A(E_7)` and `A(E_8)` have the permutational property.
2. **Every spherical type.** By the established conditional
   `spherical-artin-boone-higman-reduces-to-e6-e7-e8`, `A(Γ)` then has it. That
   reduction goes through Crisp's embedding into products of A, D and E factors
   and closure of the property under direct products.
3. **Envelope.** By `type-a-action-gives-boone-higman-for-subgroups`, `A(Γ)`
   embeds in a finitely presented simple group. QED
