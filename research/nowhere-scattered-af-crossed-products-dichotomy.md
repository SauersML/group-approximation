---
rg: 2
id: nowhere-scattered-af-crossed-products-dichotomy
kind: claim
title: Reduced crossed products of unital AF algebras without elementary subquotients by minimal properly outer actions are stably finite or purely infinite
distinct_from:
  simple-coefficient-crossed-products-dichotomy: that requires a simple coefficient algebra with state-ordered dense K_0; this allows non-simple AF coefficients with an arbitrary ideal lattice, provided no subquotient is elementary.
  rainone-type-semigroup-crossed-product-dichotomy: that proves the dichotomy when the type semigroup is almost unperforated; this proves it with no hypothesis on the type semigroup, for AF coefficients without elementary subquotients.
---

**Theorem.**  Let `D` be a unital separable AF algebra with no elementary
subquotient.  Let `Gamma` be a countable discrete group and
`alpha: Gamma -> Aut(D)` an action that is:

* minimal: no `Gamma`-invariant closed ideals other than `0` and `D`;
* properly outer.

Then `D rtimes_lambda Gamma` is simple, and exactly one of the following holds.

1. `D` has a `Gamma`-invariant tracial state.  Every such state is faithful,
   and `D rtimes_lambda Gamma` has a faithful tracial state and is stably finite.
2. `D rtimes_lambda Gamma` is purely infinite.

**Coefficient algebras covered.**
* `C(X) tensor B`, for `X` compact, metrizable and totally disconnected and `B`
  a UHF algebra, with actions that need not be of product form.
* Every non-simple AF algebra none of whose subquotients is elementary.

**What is new, and what was known.**
* Rainone's Theorem 4.22 needs the type semigroup `S(D, Gamma, alpha)` to be
  almost (weakly) unperforated.  `coinvariant-tarski-lemma-minimal-nowhere-scattered`
  supplies, for all such `D`, the weaker property Rainone isolates on page 33
  (infinite elements are properly infinite).  The division axiom it needs is
  `af-k0-order-divisible-iff-no-elementary-subquotient`.
* Product actions `beta tensor id` on `C(X) tensor B` give
  `(C(X) rtimes_lambda Gamma) tensor B`, which is `Z`-stable.  There the
  dichotomy already follows from Rordam's theorem on simple `Z`-stable
  algebras.  The new cases are actions not of this tensor form, and
  coefficient algebras not of the form `D_0 tensor UHF` with a product action.
* For amenable `Gamma`, case 1 always holds: `Gamma` fixes a point of the
  trace simplex.  So case 2 needs a non-amenable group.

Status: proved in the route below, unreviewed.  Novelty is checked against
Rainone 2017 only, which poses the needed property as a question on page 33.
Later literature is unchecked.

**Relevance to Problem XXIX.**  Consider a mixed simple real-rank-zero algebra
of the form `D rtimes_lambda Gamma`, with `D` unital AF and the action minimal
and properly outer.  Then `D` must have an elementary subquotient, for example
`D = C(X)` with `X` a Cantor space, or an AF algebra with a finite-dimensional
representation of some corner.  The division mechanism fails exactly there
(`af-k0-order-divisible-iff-no-elementary-subquotient`).  This regime contains
Rainone's question (page 33) whether a free minimal action of `F_2` on the
Cantor set can have a type semigroup that is not almost unperforated.  He notes
that the Ara--Exel examples are not minimal.
