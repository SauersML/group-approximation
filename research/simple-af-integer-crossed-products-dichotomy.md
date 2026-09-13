---
rg: 2
id: simple-af-integer-crossed-products-dichotomy
kind: claim
title: Integer crossed products of simple non-elementary AF algebras by properly outer automorphisms are stably finite or purely infinite
distinct_from:
  brown-af-automorphism-crossed-product-equivalence: that characterizes stable finiteness (equivalently AF-embeddability) of AF integer crossed products; this proves that when the AF coefficient algebra is simple and the crossed product is simple, failure of stable finiteness forces pure infiniteness, with no mixed case.
  stw29-separative-projection-monoid-dichotomy: that derives the dichotomy from separativity of V(A); this derives it for D rtimes Z from a Tarski-type argument in the coinvariant monoid of K_0(D), without knowing V(D rtimes Z).
---

**Theorem.**  Let `D` be a separable simple non-elementary AF algebra, unital
or not, and let `alpha in Aut(D)` have every nonzero power `alpha^n` properly
outer.  Put `A = D rtimes_alpha Z`, which is simple.  Exactly one of the
following holds.

1. `D` admits a nonzero `alpha`-invariant densely finite lower semicontinuous
   trace, and `A` is stably finite.
2. `A` is purely infinite, and every nonzero projection of `D tensor K` is
   infinite in `A tensor K`.

In particular no such crossed product contains both a nonzero finite and an
infinite projection.  No real rank hypothesis on `A` is used.

**Credit and scope.**  The type-semigroup framework is Rainone's
(`rainone-type-semigroup-crossed-product-dichotomy`).  The new input is
`coinvariant-tarski-lemma-simple-dimension-groups`, which removes Rainone's
almost-unperforation hypothesis.  For unital `D` the group `Z` is amenable, so
an invariant tracial state always exists and case 1 always holds (Rainone,
Corollary 4.14).  The interesting case 2 is therefore non-unital, e.g. stable
UHF-type `D` with `alpha` scaling the trace; Rainone's paper assumes unital
coefficients.  Unital coefficients with non-amenable groups are covered by
`simple-coefficient-crossed-products-dichotomy`.

Status: proved in the route below, unreviewed.  Novelty beyond Rainone 2017 is
unverified.

**Relevance to Problem XXIX.**  Rordam's separable nuclear mixed example is
`D rtimes_alpha Z` with `D` a non-simple inductive limit of type I algebras
carrying Euler-class data (`rordam-mixed-examples-not-real-rank-zero`).  Simple
zero-dimensional coefficients can never produce the mixed phenomenon.

## Attempts

* Non-simple AF `D` with no nontrivial `alpha`-invariant ideal.  The type
  semigroup is still simple, but (U) and (O) fail, because states of `K_0(D)`
  need not be faithful.  The division argument needs a margin for the defect
  `e` uniform across the ideal lattice.  For a `Z`-chain of ideals shifted by
  `alpha` with lexicographic order, every element is directly infinite
  (moving one piece up the chain has a strictly positive top term), so the
  obstruction can only come from non-lexicographic twisted orders.
