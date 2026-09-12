---
rg: 2
id: thompson-v-kl-from-leavitt-kl
kind: route
title: Kervaire--Laudenbach over the Leavitt unit group gives it over Thompson's V
target: kl-holds-over-thompson-v
requires: [kl-holds-over-binary-leavitt-unit-group, leavitt-cylinder-swaps-generate-thompson-in-el]
---

Let `w in V * <t>` be nonsingular. By
`leavitt-cylinder-swaps-generate-thompson-in-el`, `V <= R^x` for
`R = L_(F_2)(1,2)`.

- The composite `V -> R^x -> R^x_w` is injective. The first map is an
  inclusion, and the second is injective by the prerequisite applied to `w`
  read over `R^x`.
- The same composite factors as `V -> V_w -> R^x_w`, through the map induced
  by the inclusion.

The first factor of an injective composite is injective, so `V -> V_w` is
injective.

This is the contrapositive of `leavitt-kl-violation-from-thompson-v-violation`.
It is recorded as a route so that the graph shows the dependence of the
positive Leavitt root on V. The converse is not known: a proof over V says
nothing about equations whose coefficients leave V.
