---
rg: 2
id: binary-jacobson-closing-root-fold-proof
kind: route
title: Use the closing root to identify both Weyl-sign domains with one range
target: binary-jacobson-closing-root-folds-head-two-to-one
requires:
  - binary-jacobson-naive-head-polar-is-balanced-return
  - binary-jacobson-head-weyl-cut-is-native-pi-source
---

The commutator relation

```text
[x_12(1),x_23(Q)]=x_13(Q)                               (1)
```

shows that `b=x_12(1)` conjugates `Y=x_23(Q)` to
`x_13(Q)Y`.  The root `b` commutes with the head itself, so it preserves
`P`; on `P`, equation `(1)` says that it conjugates `Y` to `-Y`.  Hence

```text
bE_-b^*=E_+.                                             (2)
```

The support equations for `R` now give

```text
R_+^*R_+=bR^*Rb=bE_-b=E_+,
R_+R_+^*=RR^*=F.                                        (3)
```

Moreover

```text
R_-R_+^*=RbR^*=R E_- b E_- R^*=0,                       (4)
```

because `bE_-b=E_+` and `E_-E_+=0`; the adjoint gives the other cross
term.  Equations `(3)--(4)` imply

```text
TT^*=(1/2)(F+F)=F.                                      (5)
```

The balanced-return theorem gives `rank(F)=rank(E_-)`, and the sign-swap
argument gives `rank(E_-)=rank(E_+)=rank(P)/2`, proving `(JCF4)`.

Finally the Steinberg root relations show that `b` commutes with the three
listed native packet roots and give `(JCF5)`.  Since

```text
x_13(1)=x_13(Q)x_13(ST)
```

and `x_13(Q)` acts as `-1` on `P`, the residual fold gauge is exactly the
tail-center stated in the claim.
