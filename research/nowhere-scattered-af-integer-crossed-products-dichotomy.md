---
rg: 2
id: nowhere-scattered-af-integer-crossed-products-dichotomy
kind: claim
title: Integer crossed products of AF algebras without elementary subquotients by minimal automorphisms with properly outer powers are stably finite or purely infinite
distinct_from:
  simple-af-integer-crossed-products-dichotomy: that requires the AF coefficient algebra to be simple; this allows non-simple, possibly non-unital AF coefficients with any ideal lattice, provided no subquotient is elementary.
  nowhere-scattered-af-crossed-products-dichotomy: that treats unital coefficients and arbitrary countable groups through Rainone's framework; this treats possibly non-unital coefficients and the group Z, where the interesting case needs non-unital coefficients.
---

**Theorem.**  Let `D` be a separable AF algebra, unital or not, with no
elementary subquotient.  Let `alpha in Aut(D)` leave no closed ideal other than
`0` and `D` invariant, with every nonzero power `alpha^n` properly outer.  Put
`A = D rtimes_alpha Z`, which is simple.  Exactly one of the following holds.

1. `D` admits a nonzero `alpha`-invariant densely finite lower semicontinuous
   trace, and `A` is stably finite.
2. `A` is purely infinite, and every nonzero projection of `D tensor K` is
   infinite in `A tensor K`.

No real rank hypothesis on `A` is used.

**Examples.**
* `D = C_0(Y) tensor B tensor K` with `Y` locally compact and totally
  disconnected, `B` UHF, and `alpha` a minimal homeomorphism of `Y` twisted by
  automorphisms that scale the trace of `B tensor K`.
* Non-simple stable AF algebras with non-lexicographic ideal lattices.

Rordam's nuclear mixed example has this crossed-product shape, but with
non-zero-dimensional, type I building blocks carrying Euler classes
(`rordam-mixed-examples-not-real-rank-zero`).  The theorem shows that no
zero-dimensional coefficient algebra of this kind, without elementary
subquotients, can imitate it.

Status: proved in the route below, unreviewed.  Novelty beyond Rainone 2017
and Rordam 2005 is unchecked.
