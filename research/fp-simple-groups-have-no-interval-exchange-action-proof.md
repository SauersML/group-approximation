---
rg: 2
id: fp-simple-groups-have-no-interval-exchange-action-proof
kind: route
title: Interval exchange groups are LEF, finitely presented LEF groups are residually finite, and infinite simple groups are not
target: fp-simple-groups-have-no-interval-exchange-action
requires:
  - interval-exchange-groups-are-lef
  - finitely-presented-lef-groups-are-residually-finite
---

Let `S` be finitely presented, infinite and simple, and `rho : S -> IET(T)` a
homomorphism.

1. `ker rho` is normal, so it is trivial or `S`. Suppose it is trivial. Then `rho(S)` is
   a finitely generated group of interval exchanges isomorphic to `S`.
2. By `interval-exchange-groups-are-lef`, `S` is LEF.
3. By `finitely-presented-lef-groups-are-residually-finite`, `S` is residually finite.
4. A nontrivial residually finite group has a proper normal subgroup of finite index. `S`
   is simple, so that subgroup is trivial, and `S` is finite. Contradiction.

So `rho` is trivial. Interval exchanges of `[0, 1)` are interval exchanges of `T` with a
breakpoint at `0`, so the same holds there. ∎
