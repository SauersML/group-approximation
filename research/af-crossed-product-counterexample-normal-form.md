---
rg: 2
id: af-crossed-product-counterexample-normal-form
kind: claim
title: A mixed simple crossed product of a unital AF algebra by a minimal properly outer action needs an elementary subquotient, a non-amenable group and a finite class with a paradoxical multiple in a non-separative type semigroup
distinct_from:
  stw29-counterexample-level-two-fingerprint: that gives the normal form of an arbitrary real-rank-zero counterexample through its projection monoid; this gives the extra constraints on counterexamples of crossed-product form, with AF coefficients, read through the coefficient type semigroup.
  nowhere-scattered-af-crossed-products-dichotomy: that proves the dichotomy for coefficients without elementary subquotients; this lists everything a crossed-product counterexample must have, including where the coefficient algebra must break the division mechanism.
---

**Theorem.**  Let `D` be a unital separable AF algebra, `Gamma` a countable
discrete group, and `alpha` a minimal properly outer action.  Suppose
`A = D rtimes_lambda Gamma` (simple) is neither stably finite nor purely
infinite.  Let `Sigma = S(D, Gamma, alpha)` be Rainone's type semigroup.

1. `D` has an elementary subquotient.
2. `Gamma` is non-amenable, and `D` has no `Gamma`-invariant tracial state.
3. `Sigma` has no nontrivial state, and `Sigma` is not purely infinite.
4. There is a nonzero projection `p in D` that is finite in `A`, and
   `theta = [p]` has the following properties:
   * it is finite in `Sigma`;
   * `(k+1) theta <= k theta` for some `k >= 1`;
   * some multiple of `theta` is properly infinite.
5. `Sigma` is not separative: there are `x != y` with `2x = x + y = 2y`.
6. `D = C(X)` with a free, minimal, amenable action of a group with paradoxical
   towers is impossible (`stw99-xxxii-holds-for-paradoxical-tower-groups`).
   So is `D = C(X)` with a group that has a normal infinite cyclic or locally
   finite subgroup acting minimally on `X`
   (`minimal-normal-cyclic-subgroup-cantor-dichotomy`,
   `smoothing-normal-subgroup-cantor-dichotomy`).
   So a commutative-coefficient design needs a group with no such normal
   subgroup, and either no known paradoxical towers or an action that is not
   free or not amenable.
7. If moreover `A` has real rank zero, then `M_n(A)` contains a nonzero finite
   and an infinite projection.  This answers Problem XXIX negatively and
   carries `stw29-counterexample-level-two-fingerprint`.

**Where designs must go.**  Part 1 is the sharp threshold of the division
mechanism (`af-k0-order-divisible-iff-no-elementary-subquotient`).
Parts 3--5 say the type semigroup of the coefficient action must be a simple
monoid in which Tarski's paradoxical multiples cannot be rounded down to a
single copy.  For `D = C(X)` this is the open claim
`measure-free-minimal-cantor-action-with-finite-clopen-type`.  Part 4 alone
does not certify finiteness in `A`, because the monoid map
`Sigma -> V(A)` can make finite classes infinite.  A counterexample also needs
an analytic finiteness certificate in the crossed product.

Status: proved in the route below, unreviewed.
