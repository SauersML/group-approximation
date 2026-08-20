---
rg: 2
id: adjoint-supertrace-cannot-pay-hs-selection-load-proof
kind: route
title: Compare one operator-space direction with a balanced carrier cut
target: adjoint-supertrace-cannot-pay-hs-selection-load
requires: []
---

Take even `d` and let

```text
x = diag(1,...,1,-1,...,-1)
```

with `d/2` entries of each sign.  In normalized matrix trace,

```text
tau_d(x)=0,
||x||_2=1.
```

The one-dimensional subspace `E=Cx subset H=M_d` has orthogonal projection
of rank one as an operator on the `d^2`-dimensional Hilbert space `H`.
Consequently its normalized supertrace is

```text
tr_H(P_E)=1/d^2.                                        (1)
```

But the positive spectral cut

```text
q=1_(0,infinity)(x)
```

has rank `d/2`, hence carrier trace

```text
tau_d(q)=1/2.                                           (2)
```

Thus no constant independent of `d` can bound the carrier mass of spectral
cuts supported by a low-dimensional operator-space sector in terms of the
normalized supertrace dimension of that sector.

The same calculation does not depend on how small the Rayleigh energy assigned
to `x` is: if a positive adjoint Laplacian has `x` as an eigenvector of
eigenvalue `lambda`, the operator-space first-moment contribution is
`lambda/d^2`, while the weighted-median refinement can cut carrier trace
`1/2` and its natural scale-sensitive charge is of order `sqrt(lambda)`.
There is no dimension-free comparison between those quantities.

Finally, `span{I}` gives the support version without a balanced cut:
its normalized supertrace is again `1/d^2`, while the support projection of
its nonzero vector `I` is `1`, of carrier trace one.  Hence replacing cut mass
by support mass does not repair the mismatch.
