---
rg: 2
id: finite-subspace-gluing-is-amplification-stable
kind: claim
title: Finite families of base intertwiner subspaces glue with a multiplicity-independent spectral gap
---

Let `E` be a fixed finite-dimensional Hilbert space and let

```text
M_1,...,M_r <= E
```

be fixed linear subspaces.  Put `M=intersection_i M_i`.  Then there is a
constant `C<infinity`, depending only on the base family, such that for every
finite-dimensional Hilbert space `K` and every

```text
x in E tensor K
```

one has

```text
dist(x,M tensor K)^2
 <= C sum_i dist(x,M_i tensor K)^2.                   (SUBSPACE-GLUE)
```

The same statement applies when `E` itself is a Hilbert--Schmidt operator
space such as `M_d(C)`, and `K` is an arbitrary external matrix-multiplicity
space.

Thus once a finite atlas or compiler problem has been reduced to approximate
membership in finitely many **fixed linear intertwiner spaces**, external
multiplicity cannot destroy the gluing estimate.  The only remaining work is
the finite base-space intersection and its smallest positive spectral value.