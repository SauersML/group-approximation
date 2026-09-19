---
rg: 2
id: binary-jacobson-balanced-target-redesign-proof
kind: route
title: Conjugate the native packet by the balanced (1,3) block and compute its diagonal center
target: binary-jacobson-balanced-target-redesign-contains-mixed-root
requires:
  - binary-jacobson-head-sector-has-native-two-qubit-packet
  - binary-jacobson-first-alternating-ts-closure-relation
  - binary-jacobson-first-alternating-polar-is-half-supported
---

The Jacobson identities

```text
Q^2=Q,       QS=0,       TQ=0,       Q+ST=1,       TS=1
```

give

```text
[[Q,S],[T,0]]^2=I,                                        (1)
```

so the displayed block defines an involution `g`.  Conjugation of a matrix
unit is computed from its transformed source column and target row.

For `x_12(Q)` and `x_14(Q)`, the transformed source column is
`Q e_1+T e_3`; multiplication by the coefficient `Q` kills its second term
because `TQ=0` and leaves `Q^2=Q`.  Thus both Q-labelled roots are fixed.
The row `e_3^*g` equals `T e_1^*`, while `g e_2=e_2` and `g e_4=e_4`.
Consequently

```text
g x_23(1)g=x_21(T),       g x_43(1)g=x_41(T),             (2)
```

which proves `(JBT1)`.

Inside the `(1,3)` block, direct multiplication gives

```text
[[Q,S],[T,0]] [[1,Q],[0,1]] [[Q,S],[T,0]]
  =[[1+QT,0],[0,1]].                                      (3)
```

This is `(JBT2)`.  Since `TQ=0`, one has `(QT)^2=0`, so the right side of
`(3)` is indeed an involution.  It is the common center of `(JBT1)` by
conjugacy.

Finally `c_T` acts on a same-row root by left multiplication of its
coefficient by `1+QT`.  It fixes `x_13(Q)` because `QTQ=0`, but

```text
QT(SQ)=Q(TS)Q=Q.                                         (4)
```

Hence conjugation multiplies `x_13(SQ)` by `x_13(Q)`, proving `(JBT3)`.
Put `v=x_13(SQ)` and `e=F_+`.  The raw range has

```text
we=-e,          ve=-e.                                   (5)
```

Set `A=e c_T e`.  Right multiplication by `v` gives `Av=-A`.  On the other
hand `(JBT3)` gives `c_Tv=wv c_T`, and therefore

```text
Av=e c_T v e=e wv c_Te=+A,                              (6)
```

because `wv=+1` on `e`.  Over the complex representation space `(6)` and
`Av=-A` force `A=0`, proving `(JBT4)`.  The packet fullness on the negative
`c_T` cut is inherited exactly from the native packet under conjugation,
completing the proof.
