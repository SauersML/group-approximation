---
rg: 2
id: canonical-infinite-subgroup-adjoint-density-proof
kind: route
title: Average finitely many canonically orthogonal adjoint unitaries
target: canonical-infinite-subgroup-has-zero-adjoint-fixed-density
requires: []
---

Fix `L` distinct elements `h_1,...,h_L in H` and set

```text
A_n=(1/L)sum_i S_n(h_i).
```

Equation `(CIA1)` for this fixed finite list gives

```text
||A_nE_n-E_n||_2->0.                                  (CIA3)
```

Right multiplication by a projection is an `L^2` contraction, so

```text
sqrt(tr(E_n))=||E_n||_2
 <=||A_nE_n||_2+o(1)
 <=||A_n||_2+o(1).                                    (CIA4)
```

For adjoint matrices,

```text
tr_(d_n^2)(S_n(h_i)^*S_n(h_j))
 =|tr_(d_n)(u_n(h_i)^*u_n(h_j))|^2.                   (CIA5)
```

Asymptotic multiplicativity replaces the scalar trace on the right by that
of `u_n(h_i^(-1)h_j)` up to `o(1)`.  Canonical trace convergence makes it
`1+o(1)` for `i=j` and `o(1)` for `i!=j`.  Consequently

```text
||A_n||_2^2
 =(1/L^2)sum_(i,j)tr(S_n(h_i)^*S_n(h_j))
 ->1/L.                                               (CIA6)
```

Equations `(CIA4)--(CIA6)` give

```text
limsup_n tr(E_n)<=1/L.
```

The infinite group `H` contains such a distinct list for every `L`, hence
the limsup is zero.  This proves `(CIA2)`.

