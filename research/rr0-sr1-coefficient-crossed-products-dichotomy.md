---
rg: 2
id: rr0-sr1-coefficient-crossed-products-dichotomy
kind: claim
title: Reduced crossed products of exact real rank zero stable rank one algebras with unperforated, integer-layer-free K_0 by minimal properly outer actions are stably finite or purely infinite
distinct_from:
  nowhere-scattered-af-crossed-products-dichotomy: that treats AF coefficients; this treats every unital separable exact real-rank-zero stable-rank-one coefficient algebra whose K_0 is unperforated and has no order-subquotient isomorphic to the integers.
  simple-coefficient-crossed-products-dichotomy: that needs simple coefficients with state-ordered dense K_0; this allows arbitrary ideal lattices and replaces the state axioms by unperforation and the absence of integer layers.
---

**Theorem.**  Let `A` be a unital separable exact C\*-algebra of real rank zero
and stable rank one.  Assume:

* `K_0(A)` is unperforated;
* `K_0(A)` has no order-subquotient order-isomorphic to `(Z, N)`.

Let `Gamma` be countable discrete and `alpha` a minimal, properly outer action.
Then `A rtimes_lambda Gamma` is simple, and exactly one of the following holds.

1. `A` has a `Gamma`-invariant tracial state.  It is faithful, and the crossed
   product is stably finite.
2. The crossed product is purely infinite.

**Coefficient algebras covered.**
* Unital AF algebras without elementary subquotients.
* `C(X) tensor A_theta` for a totally disconnected compact metrizable `X` and
  an irrational rotation algebra `A_theta`.  Here `K_0 = C(X, Z + theta Z)`
  with the pointwise order, and the actions need not be of product form.
* Non-simple real-rank-zero AT or AH algebras of stable rank one with
  unperforated `K_0` and no integer layers.

**Boundary of the method.**  The coinvariant division mechanism needs exactly
three things of `K_0` of the coefficient algebra: Riesz refinement (automatic
here), unperforation, and the absence of `(Z, N)` layers
(`dimension-group-divisible-iff-no-integer-subquotient`).  Designs for a mixed
crossed product with real-rank-zero, stable-rank-one coefficients therefore
need either perforated `K_0` or an integer layer, for example a
one-dimensional quotient of some corner.  Coefficient algebras without
cancellation of projections lie outside Rainone's framework altogether.
Rordam's nuclear example uses non-zero-dimensional type I building blocks
(`rordam-mixed-examples-not-real-rank-zero`).

Status: proved in the route below, unreviewed.  Novelty unchecked.
