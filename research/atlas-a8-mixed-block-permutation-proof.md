---
rg: 2
id: atlas-a8-mixed-block-permutation-proof
kind: route
title: Split the regular Fourier blocks into transport cells and match their bases
target: atlas-a8-mixed-block-transport-has-permutation-models
requires:
  - regular-chart-wedderburn-coefficient-compiler
  - unitary-block-energy-transport
  - weighted-unitary-hall-deficit-gap
---

The two archived exact characteristic-zero A8 irrep audits cover all
fourteen irreducibles.  Non-self-conjugate `S8` partition pairs restrict to
the ten degrees

```text
1,7,14,20,21,28,35,56,64,70.
```

The self-conjugate degree-`90` and degree-`42` Specht modules split on `A8`
into pairs of degrees `45,45` and `21,21`.  This yields `(MBT1)`, and direct
addition gives

```text
sum d_sigma^2=20160,          sum d_sigma=448.
```

`regular-chart-wedderburn-coefficient-compiler` gives rank `d_sigma k` for
each minimal projection, proving `(MBT2)`.

For `(MBT3)`, partition an orthonormal basis of every source block `p_v H`
into subsets `B_(u,v)` of sizes `n_(u,v)`.  Partition an orthonormal basis of
every target block `q_u H` into subsets `C_(u,v)` of the same sizes.  The
margin equations say these subsets exhaust the respective bases.  Choose a
bijection `B_(u,v)->C_(u,v)` for every pair and take their disjoint union.
Its permutation matrix is a unitary `U`.  The block `q_u U p_v` is a partial
permutation of rank and unnormalized Frobenius-square `n_(u,v)`, which proves
`(MBT4)` after division by `20160k`.

For a rational transport plan `mu`, choose `k` so every
`n_(u,v)=20160k mu_(u,v)` is integral.  The prescribed marginals make
`(MBT3)` automatic.  Rational points are dense in the rational polytope,
giving the closure assertion.

Finally every source or target set has weight

```text
(1/20160) sum_(vertices) d_vertex.
```

The difference of two such weights is an integer multiple of `1/20160`.
If positive it is at least that value, proving `(MBT5)`.
