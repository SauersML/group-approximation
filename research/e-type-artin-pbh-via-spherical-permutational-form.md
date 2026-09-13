---
rg: 2
id: e-type-artin-pbh-via-spherical-permutational-form
kind: route
title: The E types are spherical, so the spherical permutational theorem gives them type (A) overgroups
target: e-type-artin-groups-satisfy-permutational-boone-higman
requires:
  - spherical-artin-groups-satisfy-permutational-boone-higman
---

The Coxeter groups `W(E_6)`, `W(E_7)` and `W(E_8)` are finite, so `A(E_6)`,
`A(E_7)` and `A(E_8)` are Artin groups of spherical type. By
`spherical-artin-groups-satisfy-permutational-boone-higman`, each embeds in a
group admitting an action of type (A). ∎

The argument goes through linearity over `Q(x,y)`, not through Aut(F_n) or the
Crisp reduction. So attempt 1 of the target (geometric monodromy) is not needed.
