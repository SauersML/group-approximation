---
rg: 2
id: thompson-v-acylindrically-hyperbolic-subgroups-lack-z2
kind: claim
title: No acylindrically hyperbolic subgroup of Thompson's group V contains Z^2
distinct_from:
  z2-free-z-does-not-embed-in-thompson-v: that is the non-embedding of one free product; this uses it to exclude Z^2 from every acylindrically hyperbolic subgroup of V
  thompson-t-free-product-subgroups-have-no-disjoint-pair: that excludes Z^2 from free-product subgroups of V by the Kurosh theorem; this excludes it from acylindrically hyperbolic subgroups by a ping-pong on a hyperbolic space
artifacts:
  - research/artifacts/thompson-t-disjoint-pair-witness-obstructions-2026-09-16.md
---

Let `H ≤ V` be acylindrically hyperbolic, that is, `H` admits a non-elementary acylindrical
action on a hyperbolic space (Osin, arXiv:1304.1246v4, Definition 1.3 and condition (AH2)).
Then `H` contains no subgroup isomorphic to `Z^2`.

The same proof shows more generally that if a group `G` does not contain `Z^2 ∗ Z`, then no
acylindrically hyperbolic subgroup of `G` contains `Z^2`.

**Consequences.**
- `T` and `V` are not acylindrically hyperbolic, since both contain `Z^2`.
- No acylindrically hyperbolic subgroup of Thompson's group `T` contains two nontrivial
  elements with disjoint supports on the circle. Such a pair generates `Z^2`, and
  `T ≤ V`. So the class "acylindrically hyperbolic groups with trivial amenable radical",
  which are C*-simple, supplies no witness for
  `thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`.

Proof: route `thompson-v-ah-subgroups-lack-z2-via-bleak-salazar-diaz`.
