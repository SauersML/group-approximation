---
rg: 2
id: arbitrarily-complex-fp-simple-via-hard-type-a-actors
kind: route
title: Put a hard type (A) actor inside its twisted Brin-Thompson group and transfer hardness upward
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires: [type-a-actors-with-arbitrarily-hard-word-problem, twisted-brin-thompson-finite-presentation-criterion]
---

Fix a recursive `T` and put `T+(m) = m + max_(k<=m) T(k)`.

1. **A hard actor.** `type-a-actors-with-arbitrarily-hard-word-problem`, applied
   to `T+`, gives a faithful type (A) action of `G` on `S` whose word problem is
   outside `F(T+)`.
2. **The host.** By `twisted-brin-thompson-finite-presentation-criterion`,
   `SV_G` is finitely presented. Faithfulness makes it simple, and it contains
   `G` as the single-branch elements `tau_g`.
3. **Transfer.** A word-problem algorithm for `SV_G` in time
   `C*T(C*l) + C*l + C` gives one for `G` in `F(T+)`, by the length-linear
   substitution of `complexity-bounded-host-classes-are-not-universal-proof`.
   This contradicts step 1.

So `SV_G` beats `T`. By (c) of `twisted-brin-thompson-wp-equals-actor-orbit-problem`,
this route and its premise are equivalent: finitely presented twisted
Brin--Thompson hosts can beat every recursive bound only if their actors do. `∎`
