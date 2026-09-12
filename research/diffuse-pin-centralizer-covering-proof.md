---
rg: 2
id: diffuse-pin-centralizer-covering-proof
kind: route
title: Cut the diffuse spectrum into equal-mass blocks and cover the block unitary groups
target: diffuse-pin-centralizer-has-zero-quadratic-covering
requires: []
---

Fix an integer `m`.  Partition the spectrum of `a` into `m` intervals whose
spectral projections all have trace `1/m`, choosing endpoints outside the
atomic support.  Let `P_{j,d}` be the corresponding spectral projections of
`A_d`.  Every unitary commuting with `A_d` is block diagonal for this
partition.  A Szarek net for each block unitary group gives, for a universal
constant `C`,

```text
K_(2 epsilon)({U:[U,A_d]=0},||.||_infinity)
 <= product_j (C/epsilon)^(rank(P_{j,d})^2).             (DPP1)
```

The microstate convergence and the endpoint choice give

```text
limsup_d tr(P_{j,d}) <= 1/m,
```

hence

```text
limsup_d d^(-2) log K_(2 epsilon)
 <= log(C/epsilon) limsup_d sum_j tr(P_{j,d})^2
 <= log(C/epsilon)/m.                                   (DPP2)
```

Letting `m->infinity` proves `(DPC1)`.  This is Hayes' diffuse-pin
centralizer estimate (Lemma A.3 of arXiv:1505.06682v5), with the short proof
recorded here because the orbit application is load-bearing.

For tuples with `max_x ||X_{d,x}||_infinity<=R`, conjugation is Lipschitz:

```text
||U*X_d U-V*X_d V||_2 <= 2 R sqrt(|F|) ||U-V||_infinity. (DPP3)
```

Push a centralizer net through this map to obtain `(DPC2)`.  Finally cover
each of the `N_d` orbits and take their union.  Its covering number is at most
`N_d` times the maximum orbit covering number; after dividing logarithms by
`d^2`, the first term vanishes by hypothesis and the second by `(DPC2)`,
proving `(DPC3)`.
