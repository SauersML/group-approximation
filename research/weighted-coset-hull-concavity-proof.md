---
rg: 2
id: weighted-coset-hull-concavity-proof
kind: route
title: Compute each three-cycle residual and apply concavity to p versus p-cubed
target: weighted-coset-hulls-are-energy-sublinear
requires:
  - displacement-carrier-has-p-fold-bs-hull
---

On one summand let `A_i=Y U_i`, where

```text
U_1=S^2,                 U_2=RS.
```

The exact endpoint relations give `A_i^3=1`.  Neither `A_i` lies in the
dihedral subgroup `D=<r,x>`: otherwise cancellation of the Weyl/torus
factor would put the nontrivial unipotent `s` or `s^2` in `D`.  Hence the
three cosets

```text
D, A_iD, A_i^2D
```

are distinct.  Their normalized indicators are orthonormal.  With
`C=1-2Q` and `XU_i=CA_i`,

```text
(CA_i)^3
 =C (A_i C A_i^(-1)) (A_i^2 C A_i^(-2))
 =1-2(Q+A_iQA_i^(-1)+A_i^2QA_i^(-2)).                  (WCP1)
```

Thus each cubic residual is `-2` on a three-dimensional space and zero on
its orthogonal complement.  Its Frobenius square is exactly `12`, proving
`(WCH2)`.

For `p>=3`,

```text
d_p=p(p^2-1)/2 >=p^3/4,
p <=4^(1/3)d_p^(1/3).                                  (WCP2)
```

Therefore Jensen's inequality for the concave function `t^(1/3)` gives

```text
sum_j p_j
 <=4^(1/3) sum_j d_j^(1/3)
 <=4^(1/3) N^(2/3)D^(1/3).                             (WCP3)
```

Divide by `D` and substitute `N=E/24` to obtain `(WCH4)`.
The support of a block off-diagonal corner relative to `K` lies in
`K+YK`, of rank at most `2 rank(K)`; the standard reflection polarization
estimate then gives `(WCH5)`.
