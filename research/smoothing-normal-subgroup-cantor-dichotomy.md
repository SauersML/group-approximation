---
rg: 2
id: smoothing-normal-subgroup-cantor-dichotomy
kind: claim
title: A normal subgroup acting minimally whose type semigroup is a dimension group cone forces properly infinite paradoxical classes, which covers normal locally finite subgroups
distinct_from:
  minimal-normal-cyclic-subgroup-cantor-dichotomy: that treats a normal infinite cyclic subgroup through Kakutani-Rokhlin towers; this isolates the property of the normal subgroup that the argument uses and proves it also for locally finite normal subgroups, through orbit sums.
---

**Smoothing hypothesis (SM).**  A countable group `Gamma` acts on a Cantor
space `X`, and `H` is a normal subgroup with the following properties.

* `H` acts minimally on `X`.
* The type semigroup `S(X, H) = C(X, N) / ~_H` is cancellative.
* Its Grothendieck group `K^0(X, H)`, with positive cone `S(X, H)`, is a
  noncyclic dimension group.

**Theorem.**  Under (SM):

1. `S(X, Gamma)` is the type semigroup of `Gamma / H` acting on `K^0(X, H)` by
   order automorphisms.
2. Every nonzero class of `S(X, Gamma)` with an infinite multiple is properly
   infinite, and `S(X, Gamma)` is purely infinite iff there is no invariant
   probability measure.
3. If the action is topologically free, `C(X) rtimes_lambda Gamma` is simple
   and either stably finite (an invariant measure exists) or purely infinite.

**(SM) holds in two cases.**

* (a) `H` infinite cyclic and minimal
  (`minimal-normal-cyclic-subgroup-cantor-dichotomy`, part 1).
* (b) `H` locally finite and minimal.  Then `K^0(X, H)` is the direct limit of
  the groups of orbit-sum functions of finite subgroups `H_1 subset H_2 subset ...`,
  under the pointwise order.

**Examples for (b).**  Wreath products `A wr Lambda = (direct_sum_Lambda A) rtimes Lambda`
with `A` finite and `Lambda` arbitrary, acting so that the lamp group acts
minimally.  Other examples are groups with an infinite locally finite normal
subgroup acting minimally, for instance inside topological full groups.  As in
the cyclic case, nothing is assumed about `Gamma / H`.

**Consequence for designs.**  The commutative core
`measure-free-minimal-cantor-action-with-finite-clopen-type` must use a group
with no normal subgroup satisfying (SM).  In particular the group has no
minimally acting normal subgroup that is infinite cyclic or locally finite.

Status: proved in the route below, unreviewed.  Novelty unchecked.
