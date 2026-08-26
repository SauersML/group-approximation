---
rg: 2
id: authenticated-mixed-loop-bilinear-module-proof
kind: route
title: Row-reduce the two Fox operators on End of the defining module
target: authenticated-mixed-loop-kills-bilinear-affine-modules
requires:
  - authenticated-mixed-loop-kills-quadratic-affine-modules
---

Identify `M tensor M^*` with `End_K(M)`, with coefficient action

```text
rho(g)Z=gZg^(-1).                                      (BMP1)
```

Write

```text
Z=(z_ij)_(1<=i,j<=3).                                  (BMP2)
```

Substitute `(BMP1)` into the universal rows

```text
X=A(1-q)+B(1-s)-1,
Y=(1-u)(1-q)-h^(-1)(r-1)                              (BMP3)
```

from `(MMP3)`.  Direct elementary-matrix multiplication gives the nine
coordinates of `rho(X)Z`:

```text
-z_22,
-2z_11-2z_13+2z_22,
2z_13,
(1/2)z_11+(1/4)z_12-(3/4)z_21-(1/2)z_22,
-z_11+z_22-z_33,
(1/2)z_13-z_22-(1/2)z_23+z_33,
(1/4)z_21-z_31-(1/2)z_32,
z_22+(1/2)z_23-z_33,
-z_22.                                                  (BMP4)
```

Since `2` is invertible, `(BMP4)=0` is equivalent to

```text
z_11=z_13=z_22=z_23=z_33=0,
z_21=4z_31+2z_32,
z_12=3z_21=12z_31+6z_32.                               (BMP5)
```

No division by `3` occurs, so `(BMP5)` is valid in characteristic three.
Thus the torus row leaves precisely the two parameters `z_31,z_32`.

It is unnecessary to display all nine coordinates of the second row.  On a
matrix satisfying `(BMP5)`, its `(1,1)` and `(2,1)` coordinates are

```text
(rho(Y)Z)_11=(1/2)z_32,
(rho(Y)Z)_21=2z_31-(1/4)z_32.                          (BMP6)
```

Therefore `rho(Y)Z=0` first gives `z_32=0` and then `z_31=0`.  Equation
`(BMP5)` now gives `Z=0`, proving the common-kernel assertion in every odd
characteristic.

For reproducibility, `(BMP4)` and `(BMP6)` use only

```text
q=1-(1/2)E_21,                  s=1-(1/2)E_32,
u=1+E_13-(1/2)E_23,            r=1-E_23,
A=1+2E_12,
B=diag(2,1/2,1)(1+2E_23),      h=diag(2,1,1/2),         (BMP7)
```

and the rule `(BMP1)`; hence they can be checked entry by entry with no
representation classification.  Frobenius fixes every scalar in `(BMP7)`,
so the calculation is unchanged on all twists.  The filtration statement
then follows from the extension-closure argument `(MMP11)`.
