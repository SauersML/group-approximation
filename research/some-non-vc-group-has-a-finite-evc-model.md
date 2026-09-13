---
rg: 2
id: some-non-vc-group-has-a-finite-evc-model
kind: claim
title: Some group that is not virtually cyclic admits a finite model for the classifying space for virtually cyclic subgroups
distinct_from:
  some-fp-non-vc-group-has-property-bvc: that claim asks only for finite presentation plus BVC; this claim asks for a finite E_VC model, which is strictly stronger
---

The negation of `groups-with-finite-evc-model-are-virtually-cyclic`: a group `G`, not
virtually cyclic, with a `G`-CW model for `E_VC G` that has finitely many orbits of cells.

## Attempts

- Constraints any example must meet (von Puttkamer–Wu 1607.03790, Proposition 1.1, and the
  classes in the root): `G` has type `F_infinity`, BVC, a finite model for `E_FIN G`,
  finitely many conjugacy classes of finite subgroups; `G` is not residually finite, not
  linear, not hyperbolic, not elementary amenable, not acylindrically hyperbolic, not an
  Artin group; `H_1(G;Z)` has rank at most one.
- Any example is also a counterexample to Conjecture B (`bvc-counterexample-from-jpl-counterexample`).
  The counterexample side belongs to lane z1-07-vc-counter.
