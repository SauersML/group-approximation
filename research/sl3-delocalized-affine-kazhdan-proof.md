---
rg: 2
id: sl3-delocalized-affine-kazhdan-proof
kind: route
title: Use the affine Kazhdan group and Popa's Fourier escape criterion
target: sl3-amenable-base-has-delocalized-rigid-factor
requires: []
---

The pair `(Z^3 rtimes SL_3(Z),Z^3)` has relative property `(T)`, while the
quotient `SL_3(Z)` has property `(T)`.  The extension criterion gives property
`(T)` for `G`.  It is ICC: every nonzero translation has an infinite
`SL_3(Z)`-orbit, and conjugating a nonidentity linear part by translations
produces infinitely many affine parts.  Hence `M=L(G)` is a property-`(T)`
`II_1` factor.

If `M prec_M B`, a nonzero corner of the nonamenable factor `M` would embed
in a matrix amplification of the amenable algebra `B`.  Amenability passes to
corners and subalgebras, contradicting property `(T)` and diffuseness of `M`.

For the second non-intertwining, write elements of `G` as `(a,g)`.  Choose
translations `k_j in Z^3` escaping every finite subset and put
`v_j=lambda(k_j,1)`.  For fixed group elements `x=(a,g)` and `y=(b,h)`,
the Fourier term `x v_j y` belongs to the actor subgroup `{0} rtimes SL_3(Z)`
only if

```text
a + g k_j + g b = 0,
```

which excludes all but one value of `k_j`.  A diagonal choice of the sequence
therefore gives

```text
||E_(L(SL_3(Z)))(x v_j y)||_2 -> 0
```

for all `x,y in M`, first on the group algebra and then by `L^2`
approximation.  Popa's intertwining criterion yields
`M not_prec_M L(SL_3(Z))`, proving `(SAD1)`.

Finally the Haagerup Fourier-multiplier proof used for a Haagerup actor would
require normalized positive-definite `c_0` functions converging pointwise to
one.  Their existence is precisely the Haagerup property, which an infinite
property-`(T)` group cannot have.  The counterexample shows this missing
deformation is substantive rather than a gap in that proof.

