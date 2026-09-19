---
rg: 2
id: atlas-one-functional-gauge-pin-proof
kind: route
title: Normalize one coefficient and complexify the honest phase slice
target: atlas-one-functional-gauge-pin-cannot-create-shrinkage
requires:
  - atlas-phase-cycle-determinant-is-gauge-trivial
  - atlas-phase-jacobian-has-invertible-gauge-kernel
---

For nonzero complex numbers `z,w` with `|z|,|w|>=c`,

```text
|z/|z|-w/|w|| <= 2|z-w|/c.                            (OFP1)
```

Since `||A||_2<=1`, Cauchy--Schwarz gives

```text
|ell(U)-ell(V)|<=||U-V||_2.
```

Insert these estimates into `(OFG2)` and use the triangle inequality to get
`(OFG3)`.  The exact energy invariance follows from `(PCD4)` and the fact
that scalar multiplication leaves singular values unchanged.

At a pinned point, differentiating the real equation `Im ell(U)=0` gives
`(OFG4)`.  Because `ell(U)>0`,

```text
Im ell(U)=0,                 Im ell(iU)=ell(U)>0.
```

Thus `U in S_U` and `iU notin S_U`.  Any complex operator space containing
the honest real slice contains `U`; invertibility proves `(OFG5)` exactly as
in `(PJK2)`.  In contrast, `ell(T)=0` imposes both `Re ell(T)=0` and
`Im ell(T)=0`, so it is not the tangent equation of the circle gauge slice.

For the instability example,

```text
tr_2(U_t)=i sin(t),              tr_2(U_(-t))=-i sin(t).
```

Hence for `t>0`, the scalar pins are respectively `-i` and `i`.  The raw
matrices converge to one another as `t->0`, while their pinned versions tend
to `-i diag(1,-1)` and `i diag(1,-1)`.  Their normalized-HS distance tends
to `2`, proving `(OFG6)` and completing the dichotomy.
