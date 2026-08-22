---
rg: 2
id: pair-sum-row-square-congestion-proof
kind: route
title: Expand every assigned commutator against its exact local face
target: pair-sum-faces-have-row-square-incidence-control
requires:
  - quadratic-redundant-check-overlay-gives-uniform-face-gap
---

Use the bounded-congestion assignment `f=f(i,j)` from
`pair-sum-face-congestion-proof`.  Write `A_i=A_(f,i)`, `A_j=A_(f,j)`,
`D_i=Q_i-A_i`, and `D_j=Q_j-A_j`.  Since the local copies commute,

```text
 [Q_i,Q_j]=D_iQ_j+A_iD_j-D_jQ_i-A_jD_i.                    (PSR2)
```

For arbitrary operators `T_1,...,T_4`,
`(sum T_k)^*(sum T_k)<=4sum T_k^*T_k`.  The four squares in `(PSR2)` are

```text
 Q_jD_i^2Q_j,   D_j^2,   Q_iD_j^2Q_i,   D_i^2.             (PSR3)
```

(All `A` and `Q` are reflections.)  Sum `(PSR3)` over assigned ordered
pairs.  Each face has bounded width and receives only boundedly many pairs,
so each occurrence square appears with bounded multiplicity, either
unconjugated or conjugated by one of the boundedly many endpoint
reflections in that face.  This is precisely a fixed symmetrization
`H_inc^sym`.  Finally `I=Theta(L^2)` for the balanced original-plus-pair-sum
overlay.  Divide by `L^2` to obtain `(PSR1)`.

Taking normalized trace and using tracial invariance recovers the earlier
Hilbert--Schmidt congestion estimate.  The operator-order statement is
an algebraic strengthening, but its endpoint symmetrization need not be
covariant under the raw presentation.  Therefore it is not, by itself, a
license for a reducing physical cut; the downstream Green-edge proof uses
its normalized trace consequence.
