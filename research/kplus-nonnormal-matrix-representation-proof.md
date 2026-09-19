---
rg: 2
id: kplus-nonnormal-matrix-representation-proof
kind: route
title: Free-complexify a two-point magic unitary by a noncommuting rotation
target: finite-dimensional-kplus-does-not-factor-through-hinfinityplus
requires: []
---

In `M_2(C)`, let

```text
p=diag(1,0),        q=1-p,
v=[[p,q],[q,p]],
z=(1/sqrt(2))[[1,1],[-1,1]].                           (KNR1)
```

The matrix `v` is a magic unitary and gives the required `H_2^+`
representation.  The free-product universal property and the
free-complexification realization send the fundamental entries of `K_2^+`
to

```text
u_(ij)=v_(ij)z.                                        (KNR2)
```

But `u_(11)=pz` satisfies

```text
u_(11)u_(11)^*=p,
u_(11)^*u_(11)=z^*pz!=p.                               (KNR3)
```

Thus `u_(11)` is not normal.  Normal partial-isometry entries are among the
defining extra relations of `H_n^(infinity+)`, so this representation cannot
factor through that quotient.

