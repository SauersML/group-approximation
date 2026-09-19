---
rg: 2
id: whole-module-covariance-average-proof
kind: route
title: Average every occurring difference character on its finite sign quotient
target: whole-module-covariance-average-equals-character-transport
requires: []
---

Insert the source and target spectral projections on both sides of the
covariance defect.  Orthogonality gives

```text
d_s(m)^2
 =4 sum_(chi,psi)
    1_(psi(sm)!=chi(m)) ||P_psi C P_chi||_2^2.        (1)
```

Only finitely many difference characters

```text
m |-> psi(sm)chi(m)
```

occur.  Quotient `M` by their common kernel and average uniformly over the
finite image `M_0`.  A nontrivial sign character of a finite elementary
abelian group is balanced, whereas the difference character is trivial
exactly when `psi=s chi`.  Therefore `(1)` averages to

```text
2 sum_(psi!=s chi)||P_psi C P_chi||_2^2.              (2)
```

On the other hand, sum the squared distances in `(WCA1)` over the whole
dual, extending the finite PVM by zero.  Both PVMs have total trace one, so

```text
E_s
 =2-2 sum_chi ||P_(s chi) C P_chi||_2^2
 =2 sum_(psi!=s chi)||P_psi C P_chi||_2^2.            (3)
```

Equations `(2)--(3)` prove the exact average.  The supremum bound follows
because a finite probability average is at most the supremum.
