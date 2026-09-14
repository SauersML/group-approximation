---
rg: 2
id: kl-via-internal-closure-of-a-universal-group
kind: route
title: Solve every nonsingular equation inside one group that contains every countable group
target: kervaire-laudenbach-nonsingular-conjecture
requires: []
---

**The proposal.**
- Every countable group embeds in `Sym(N)`, and acts faithfully on a Cantor
  set, so it lies in `Homeo(C)`.
- Show that one such universal group `U` solves every nonsingular equation
  *over itself, inside itself*.
- Then for countable `G <= U` and nonsingular `w`, a root `t in U` makes
  `G -> G_w` injective.
- The root would come from structure specific to `U` — divisibility of clopen
  sets, the Hilbert hotel, genericity in a Polish group — not from satisfiability.
  So this is not the dead move of `overgroup-room-does-not-supply-a-root`, which
  only enlarges the ambient.

**Dead for both natural ambients, at every degree that matters.**
- `infinite-symmetric-groups-miss-a-unimodular-root`: `Sym(Omega)` has no root
  for `x (0 1) x (0 1) x^(-1) (0 2) = 1`, exponent sum `1`, nor for
  `x^2 (0 1) = 1`, exponent sum `2`.
- `cantor-homeomorphisms-miss-a-unimodular-root`: `Homeo(C)` has no root for
  the same exponent-sum-`1` equation, with `a, b` permuting three clopen
  copies. The adjunction group is `D_9`, and none of its actions gives the
  coefficient `S_3` orbits of sizes `1` and `3` only.
- `cantor-odometer-has-no-homeomorphism-square-root`: `Homeo(C)` has no root
  for `x^2 a^(-1) = 1` with `a` the odometer.

Every failure is at a coefficient group where Kervaire--Laudenbach holds,
because the coefficient groups are finite or cyclic. So internal closure is
strictly stronger than the conjecture, and false for these ambients.

**Why no universal ambient can work this way.** Internal solvability depends on
how the coefficients are embedded, and a group containing every countable group
contains bad embeddings of finite groups. For example, `S_3` acting with orbits
of size `1` and `3` can be embedded into essentially any such ambient. A proof
through a universal group must therefore first re-embed the coefficients, which
is the overgroup step of `overgroup-room-does-not-supply-a-root`.

**What survives.** Nothing of the internal-closure idea as stated.
- Roots found in a *chosen* universal group after re-embedding the
  coefficients are still possible.
- Any such argument must say how the re-embedding avoids the orbit-type
  obstruction of `cantor-homeomorphisms-miss-a-unimodular-root`.
