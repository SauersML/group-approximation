---
rg: 2
id: kt-wreath-lamp-cartan-proof
kind: route
title: Free ergodic Bernoulli action gives a factor with Cartan lamp algebra
target: kt-wreath-algebra-has-a-lamp-cartan
requires:
  - kt-coset-bernoulli-essentially-free
---

Item 1 is duality: `L(direct_sum_I Z/2Z) = L^infinity({-1,1}^I)`, with the
canonical trace equal to Bernoulli(1/2) integration.  For a semidirect product,
`L(N rtimes G) = L(N) rtimes G`, where `G` acts by the induced trace-preserving
automorphisms, here the coordinate permutations.

For `q = 2`, `kt-coset-bernoulli-essentially-free` gives an essentially free and
ergodic p.m.p. action `G action (X,mu)`.  For such an action the group measure
space construction `L^infinity(X) rtimes G` is a II_1 factor, and
`L^infinity(X)` is maximal abelian (freeness) and regular (it is normalized by
the implementing unitaries, which together with it generate the algebra).  It
is diffuse because `I` is infinite and the product measure is nonatomic, and it
is hyperfinite because it is abelian.  These are the standard Murray--von
Neumann and Feldman--Moore facts for free ergodic p.m.p. actions.

For general `q`, `Z_q` acts trivially and is central.  Cutting by the minimal
central projections `p_chi = |Z_q|^(-1) sum_z chi(z) u_z` gives twisted crossed
products of the free ergodic `G/Z_q` action, and the same argument applies in
each corner.
