---
rg: 2
id: simple-coefficient-crossed-products-dichotomy
kind: claim
title: Reduced crossed products of simple real rank zero stable rank one coefficient algebras with state-ordered dense K_0 are stably finite or purely infinite, for every countable group
distinct_from:
  rainone-type-semigroup-crossed-product-dichotomy: that proves the dichotomy under the extra hypothesis that the type semigroup is almost unperforated; this removes that hypothesis whenever the coefficient algebra is simple with state-ordered dense K_0, via the coinvariant Tarski lemma.
  simple-af-integer-crossed-products-dichotomy: that treats possibly non-unital simple AF coefficients and the group Z with a self-contained trace argument; this treats unital coefficients, arbitrary countable discrete groups, and general simple exact real-rank-zero stable-rank-one algebras, via Rainone's framework.
---

**Theorem.**  Let `A` be a unital separable simple exact C\*-algebra of real
rank zero and stable rank one.  Suppose `(K_0(A), K_0(A)^+, [1])` satisfies
(O) (strict positivity on states implies positivity) and (D) (dense image in
`Aff` of the state space), as in
`coinvariant-tarski-lemma-simple-dimension-groups`.  Let `Gamma` be a countable
discrete group and `alpha: Gamma -> Aut(A)` a properly outer action.  Then
`A rtimes_lambda Gamma` is simple, and exactly one of the following holds.

1. `A` has a `Gamma`-invariant tracial state, and the crossed product is stably
   finite.
2. The crossed product is purely infinite.

Example: every simple unital non-elementary AF algebra `A`, where (O) and (D)
are Effros--Handelman--Shen.

**Relation to Rainone.**  This is Rainone's Theorem 4.22 without its
hypothesis that `S(A, Gamma, alpha)` is almost unperforated.  The coinvariant
Tarski lemma supplies exactly the weaker property singled out on page 33 of
arXiv:1502.06153: infinite elements of `S` are properly infinite.  For
amenable `Gamma` an invariant tracial state always exists (fixed point on
`T(A)`; Rainone, Corollary 4.14 in the AF case), so case 2 needs a
non-amenable group.  For non-unital coefficients and `Gamma = Z`, see
`simple-af-integer-crossed-products-dichotomy`.

Status: proved in the route below, unreviewed.  Novelty beyond Rainone 2017 is
unverified; no later literature was checked.

**Relevance to XXIX.**  Any simple mixed algebra of the form
`A rtimes_lambda Gamma` with `A` of this kind is impossible, for every
countable group, amenable or not.  Mixed crossed products require
coefficient algebras whose `K_0` is not state-ordered and dense.  Examples are
non-simple coefficients with non-faithful states, or Euler-class obstructions
invisible to `K_0`, as in Rordam's `D`.
