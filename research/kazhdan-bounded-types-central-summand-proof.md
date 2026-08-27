---
rg: 2
id: kazhdan-bounded-types-central-summand-proof
kind: route
title: Sum the isolated finite-dimensional ideals in the maximal group C-star algebra
target: kazhdan-bounded-types-form-central-summand
requires:
  - kazhdan-bounded-unitary-types-are-finite
  - commutant-density-forces-bounded-type-mass
---

By Wang's theorem, each finite-dimensional irreducible representation
`sigma` of a Kazhdan group is an isolated point of the unitary dual.  The
standard ideal--spectrum correspondence gives an ideal of
`C*_max(Gamma)` whose spectrum is the singleton `{sigma}`.  This ideal is
the elementary algebra `M_(dim sigma)(C)`.  Being finite-dimensional, it is
unital; its unit `p_sigma` is a central projection in the ambient unital
C-star algebra.  In any representation `rho`, `rho(p_sigma)` is the
projection onto the `sigma`-isotypic summand.

There are only finitely many `sigma` of degree at most `K`, and their
central projections are mutually orthogonal.  Therefore

```text
p_<=K=sum_(dim sigma<=K) p_sigma
```

is a central projection and has the selection property `(KCS1)--(KCS2)`.

The left regular representation of an infinite discrete group has no
nonzero finite-dimensional subrepresentation.  Indeed its matrix
coefficients vanish at infinity, whereas a nonzero coefficient of a
finite-dimensional unitary representation is almost periodic and cannot
vanish at infinity on an infinite group.  Since the range of
`lambda_Gamma(p_sigma)` would be a sum of copies of `sigma`, every such
range is zero.  This proves `(KCS3)`.

Finally `(KCS2)` substitutes `tr(rho(p_<=K))` for `mu_K` in `(BTM3)` and
`(BTM4b)`, proving `(KCS4)`.

