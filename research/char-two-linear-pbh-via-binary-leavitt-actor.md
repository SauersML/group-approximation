---
rg: 2
id: char-two-linear-pbh-via-binary-leavitt-actor
kind: route
title: Place the linear group in the binary Leavitt unit group, then in its finitely presented type (A) actor
target: char-two-curve-linear-groups-satisfy-permutational-boone-higman
requires:
  - char-two-curve-linear-groups-satisfy-boone-higman
  - char-two-laurent-linear-groups-satisfy-boone-higman
  - binary-leavitt-unit-group-satisfies-pbh
---

Let `U = L_(F_2)(1,2)^x`.

1. **Curves.** By `char-two-curve-linear-groups-satisfy-boone-higman`, every finitely
   generated subgroup `H` of `GL_n(K)`, for `K` of characteristic two and transcendence
   degree at most one over `F_2`, embeds in `U`.
2. **Laurent and free algebras.** By `char-two-laurent-linear-groups-satisfy-boone-higman`,
   every subgroup `H` of `GL_n(F_q[t, t^-1])` or of `GL_n(F_q<x_1, ..., x_m>)`, for `q` a
   power of two, embeds in `U`.
3. **The actor.** By `binary-leavitt-unit-group-satisfies-pbh`, `U` embeds in a finitely
   presented group `Γ` admitting an action of type (A) on some set `S`.
4. **Composition.** In either case `H -> U -> Γ` is an injective homomorphism, so `H` embeds
   in `Γ`. A type (A) action is a property of the pair `(Γ, S)`, so nothing further is
   needed. ∎
