---
rg: 2
id: af-crossed-product-counterexample-normal-form-proof
kind: route
title: Traces give stable finiteness, Theorem 4.16 locates a finite projection in D, Proposition 4.17 keeps its class finite, and doubling a finite class with an infinite double breaks separativity
target: af-crossed-product-counterexample-normal-form
requires: [nowhere-scattered-af-crossed-products-dichotomy, rainone-type-semigroup-crossed-product-dichotomy, stw99-xxxii-holds-for-paradoxical-tower-groups, minimal-normal-cyclic-subgroup-cantor-dichotomy, smoothing-normal-subgroup-cantor-dichotomy]
---

The hypotheses of Rainone's Theorems 3.7, 4.13, 4.16 and 4.21 hold, as
verified in `nowhere-scattered-af-crossed-products-dichotomy-proof`.  So
`Sigma` is simple and conical (proof of `coinvariant-tarski-lemma-minimal-nowhere-scattered`,
Step 1 and the congruence paragraph, which use no divisibility).

**1.**  Otherwise `nowhere-scattered-af-crossed-products-dichotomy` makes `A`
stably finite or purely infinite.

**2.**  Suppose `tau` is a `Gamma`-invariant tracial state.  It is faithful by
minimality, so `A` is stably finite (Theorem 4.13, `(1) => (3)`).  For amenable
`Gamma`, a fixed point of the compact convex trace space `T(D)` would be such a
state.

**3.**  A nontrivial state on `Sigma` gives a faithful invariant state on
`K_0(D)`, hence an invariant tracial state (Case A of the dichotomy proof), which
is excluded by 2.  If `Sigma` were purely infinite, Theorem 4.21 `(1) => (3)`
would make `A` purely infinite.

**4.**
* If every nonzero projection of `D` were properly infinite in `A`, then `A`
  would be purely infinite by Theorem 4.16.  So some nonzero projection
  `p in D` is not properly infinite in `A`.
* In a simple algebra an infinite projection is properly infinite.  Indeed,
  if `v^* v = p`, `v v^* = p_1 < p` and `e = p - p_1`, the projections
  `v^i e v^(*i)` are orthogonal subprojections of `p`, all equivalent to `e`.
  Since `e` is full, `p <~ e tensor 1_n` for some `n`.  So `p` is subequivalent
  to two orthogonal sums of `n` of them, and `p direct_sum p <~ p`.  Hence `p` is
  finite in `A`.
* If `theta = [p]` satisfied `2 theta <= theta`, then Rainone's
  Proposition 4.17 (`(3) => (1)`, arXiv:1502.06153v1, page 28) would give
  `x, y in C_c(Gamma, D)` with `x^* x = p = y^* y`, `x x^* perp y y^*` and
  `x x^*, y y^* <= p`.  Then `p` would be properly infinite in `A`.
* In a simple conical monoid an infinite element is properly infinite
  (Step 5 of `coinvariant-tarski-lemma-minimal-nowhere-scattered-proof`).  So
  `theta` is finite.
* By 3 and Tarski (Rainone, Theorem 4.11), `(k+1) theta <= k theta` for some
  `k`, and `k >= 1` by conicality.  So `k theta = k theta + (theta + zeta)` is
  infinite, hence properly infinite.

**5.**
* If `a <= b` and `a` is infinite, then `b` is infinite.  So there is `m >= 0`
  with `u = 2^m theta` finite and `2u` infinite, hence properly infinite.
* Write `2u = 4u + w` and put `r = 2u + w`, `x = u`, `y = u + r`.  Then
  `x + y = 4u + w = 2u = 2x` and `2y = 2u + 4u + 2w = 2u + (4u + w) + w = 4u + w = 2u`.
* `x != y`: otherwise `u = u + r` with `r != 0`, contradicting finiteness of `u`.

(This is the computation of `stw29-counterexample-level-two-fingerprint`, part
(c), transplanted to `Sigma`.)

**6.**  For `D = C(X)` the action is an action on `X`.  If it is free, minimal
and amenable and `Gamma` has paradoxical towers, then `A` is a Kirchberg
algebra (`stw99-xxxii-holds-for-paradoxical-tower-groups`).  In particular `A`
is purely infinite.  If `Gamma` has a normal infinite cyclic subgroup acting
minimally on `X`, then `A` is stably finite or purely infinite by
`minimal-normal-cyclic-subgroup-cantor-dichotomy`.  The same holds for a
normal locally finite subgroup acting minimally, by
`smoothing-normal-subgroup-cantor-dichotomy`.  For commutative
coefficients, properly outer means topologically free.

**7.**  `A` is not stably finite, so some `M_n(A)` has an infinite projection.
`A` is not purely infinite, and `p` from 4 is a nonzero finite projection of
`A`, hence of `M_n(A)`.  `M_n(A)` is simple with real rank zero.
