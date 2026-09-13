---
rg: 2
id: rp-fp-infinity-host-from-fp-f-infinity-hosts
kind: route
title: "F_infinity hosts for all finitely presented groups give a recursively presented FP_infinity host of a universal group"
target: universal-fp-group-embeds-in-rp-fp-infinity-group
requires:
  - every-finitely-presented-group-embeds-in-an-f-infinity-group
---

Let `U` be a universal finitely presented group. It is finitely presented, so
the required claim gives an injective homomorphism `ι: U → K` with `K` of
type `F_∞`. `K` is finitely presented (type `F_2`), hence recursively
presented, and type `F_∞` implies type `FP_∞`. So `K` is a recursively
presented group of type `FP_∞` containing `U`.

Together with `fp-f-infinity-hosts-from-rp-fp-infinity-host` this makes the
two claims equivalent. That is a deliberate cycle: each route is a true
implication, and the equivalence is what lets `FP`-world constructions attack
`every-finitely-presented-group-embeds-in-an-f-infinity-group`.
