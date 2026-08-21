---
rg: 2
id: expander-pvm-transport-forces-dimension-or-mass-collapse
kind: claim
title: Expander transport of one PVM forces large dimension or marked-mass collapse
---

ESTABLISHED.  Let `G=(Omega,E)` be a finite `D`-regular undirected graph
whose normalized adjacency operator has spectral gap at least `gamma>0`.
Let `(P_v)_(v in Omega)` be pairwise orthogonal projections in `M_d(C)` and
put

```text
p_v=tr_d(P_v),                 mu=sum_v p_v.
```

Suppose each color `s` of a symmetric `D`-regular presentation of `G` has a
unitary `W_s` and define the total PVM transport energy

```text
E_PVM=(1/D) sum_s sum_v ||W_s P_v W_s^* - P_(s v)||_(2,d)^2.   (EP1)
```

Then

```text
E_PVM >= 2 gamma mu (1-d/|Omega|).                             (EP2)
```

Consequently, if `d<|Omega|/2`, then

```text
mu <= E_PVM/gamma.                                             (EP3)
```

The estimate is independent of `d` and `|Omega|`.  Thus a decoder which
produces one common marked PVM of mass `mu` and controls `(EP1)` by
`C epsilon^theta` already gives the desired dichotomy

```text
d >= |Omega|/2       or       mu <= (C/gamma) epsilon^theta.
```

This is the scalar endpoint required by the sparse two-matching route.  It
does not ask for uniform lower bounds on individual Fourier blocks and does
not telescope along paths.

