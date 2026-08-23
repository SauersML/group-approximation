---
rg: 2
id: regular-kazhdan-haagerup-rigidity-proof
kind: route
title: Turn the regular character into a diffuse rigid algebra and apply Popa relative Haagerup exclusion
target: regular-kazhdan-reps-avoid-haagerup-crossed-products
requires: []
---

Suppose `(RKR1)` holds and put `P={V_q:q in Q}''`.  The regular trace identity
makes the map on the group algebra

```text
sum_q c_q lambda_q  |->  sum_q c_q V_q
```

an isometry for the GNS `2`-norm.  It therefore extends to a trace-preserving
isomorphism `L(Q)=P`; in particular it is injective even when `Q` is not ICC.

The algebra `L(Q)` is diffuse for infinite `Q`.  One direct argument is that
the left regular representation of an infinite group has no nonzero
finite-dimensional subrepresentation: all of its matrix coefficients vanish
at infinity, whereas a nonzero finite-dimensional coefficient is almost
periodic and cannot vanish at infinity.  Thus `P` has no atomic central
summand.  Moreover `P` is not type I.  A finite type-I algebra is amenable,
while amenability of `L(Q)` is equivalent to amenability of `Q`; an amenable
discrete property-`(T)` group is finite, contrary to the hypothesis.  Hence
`P` has a nonzero diffuse type-II central summand.

Property `(T)` of `Q` makes `P subset M` relatively rigid.  Indeed, for any
sequence of normal subunital subtracial completely positive maps on `M`
converging pointwise to the identity, the associated pointed correspondences
give almost invariant vectors for the unitary copy `V(Q)`.  Group property
`(T)` makes them uniformly invariant on all `V_q`; the standard convexity and
Kadison estimates then give uniform `2`-norm convergence on the unit ball of
`P`.  Relative rigidity passes to a nonzero central summand of `P`.

On the other hand, Popa's relative-Haagerup theorem gives property `H`
relative to `A` for `M=A rtimes G` because `G` is Haagerup.  Since `A` is
abelian and hence type I, Popa's rigidity exclusion says that such an `M`
contains no diffuse relatively rigid finite type-II subalgebra.  Applying
this to the nonzero type-II central summand found above gives a contradiction
and proves the claim.
