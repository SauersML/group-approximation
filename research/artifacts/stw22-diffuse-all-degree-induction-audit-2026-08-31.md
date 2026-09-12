# Audit: diffuse all-finite-degree supercarrier induction

## Induction invariant

At degree d, every diffuse Stiefel space is C^d, the family is equi-LC^d,
and the explicit top-sphere radius is epsilon_0^2/1,000,000. To pass from
d-1 to d:

```text
projection S^(d-1) lift: Michael d-2 using corner LC^(d-2)
projection fill:          Stiefel LC^(d-1)
S^d supercarrier:         Michael d-1 using Grassmannian LC^(d-1)
S^d pair lifts:           Michael d-1 using corner LC^(d-1)
relative B^(d+1) bands:   Michael d using Stiefel LC^d
```

The analytic spectral lsc proof, trace reserve, carrier radius, direct
rotation, row metric, and weighted low cost are dimension-free. At each
stage only finitely many lower-degree moduli are used for existence; no
infinite-dimensional selection theorem or uniform-in-degree Michael
constant is assumed.

## Bundle consequence

For a base of finite dimension D, use only weighted degree D-1. Existing
stabilization/lower-semicontinuity and operator recovery then give exact
copies, and arbitrary replication kills every fibre-gap trace. Varying
diffuse II1 isomorphism classes cause no issue because all moduli are
factor-uniform.