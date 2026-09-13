---
rg: 2
id: minimal-normal-cyclic-subgroup-cantor-dichotomy
kind: claim
title: If a normal infinite cyclic subgroup acts minimally on the Cantor space, infinite multiples in the type semigroup are properly infinite and the crossed product is stably finite or purely infinite
distinct_from:
  stw99-xxxii-holds-for-paradoxical-tower-groups: that covers free minimal amenable actions of groups with paradoxical towers through dynamical comparison; this covers any topologically free action of any group containing a normal infinite cyclic subgroup that acts minimally, with no comparison and no condition on the rest of the group.
  nowhere-scattered-af-crossed-products-dichotomy: that needs coefficient algebras without elementary subquotients; this treats the commutative coefficient algebra C(X), where every point is an elementary subquotient, by first passing to the coinvariants of the normal subgroup.
---

**Theorem.**  Let a countable discrete group `Gamma` act on a Cantor space
`X`.  Suppose some normal subgroup `H` of `Gamma` is infinite cyclic and acts
minimally on `X`.  Let `S(X, Gamma) = C(X, N) / ~` be the type semigroup, with
clopen pieces moved by group elements.

1. `S(X, H)` is cancellative.  It is the positive cone of
   `K^0(X, H) = C(X, Z) / {h - T h}`, a simple noncyclic dimension group.
2. `S(X, Gamma)` is isomorphic to the type semigroup of the induced action of
   `Gamma / H` on `K^0(X, H)` by order automorphisms.
3. In `S(X, Gamma)`, every nonzero class with an infinite multiple is properly
   infinite.  `S(X, Gamma)` is purely infinite iff `X` has no
   `Gamma`-invariant probability measure.
4. If the action is topologically free, `C(X) rtimes_lambda Gamma` is simple
   and exactly one of the following holds.
   * There is a `Gamma`-invariant probability measure, and the crossed product
     is stably finite.
   * The crossed product is purely infinite.

**Examples.**
* `Gamma = Z x Lambda` for an arbitrary countable group `Lambda`, acting by
  homeomorphisms commuting with a minimal homeomorphism `T`.
* `Gamma = Z rtimes Lambda` with `Lambda` acting on `Z` through `+-1`, where
  each `lambda` conjugates `T` to `T^(+-1)`.

Nothing is assumed about `Lambda`: no amenability, exactness or paradoxical
towers.  Part 4 is vacuous in the purely infinite direction unless `Lambda`
permutes the `T`-invariant measures without a common fixed point.

**Where it sits.**
* The division step of `coinvariant-tarski-lemma-minimal-nowhere-scattered`
  fails for `C(X, Z)` (`af-k0-order-divisible-iff-no-elementary-subquotient`).
  The normal subgroup repairs it: its coinvariants replace the discrete group
  `C(X, Z)` by the divisible simple dimension group `K^0(X, H)`, and the lemma
  then runs on the quotient group `Gamma / H`.
* So the commutative design `measure-free-minimal-cantor-action-with-finite-clopen-type`
  needs a group with no normal infinite cyclic subgroup acting minimally.

Status: proved in the route below, unreviewed.  Novelty is unchecked: web
search was exhausted and the arXiv API was rate-limited on 2026-09-13.
