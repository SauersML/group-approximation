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

Here is the normalization with the repeats exposed.  There are
`Theta(M^2)` indexed faces: all unordered pairs of distinct original rows,
together with `Theta(M)` copies of every original row in the balanced
version.  Every indexed face is nonempty and has size at most `2q`
(distinct binary rows have nonzero symmetric difference), whence

```text
 c M^2<=I=sum_f|f|<=C_q M^2.
```

The fixed choices `a(i)` use at most `q` coordinates per original row.
Thus an original face receives `O(q^2)` assigned ordered pairs and a
pair-sum face indexed by `{a,b}` receives at most `2q^2`.  When original
faces are repeated, assign the finitely many relevant pairs to any indexed
copies; this only decreases congestion, while unused occurrence squares
remain positive terms of `H_inc`.  Consequently every occurrence square
and endpoint conjugate is counted `O_q(1)` times.  Since `M/L` is bounded
above and below, replacing `M^2` by `L^2` costs only a fixed constant.

Taking normalized trace and using tracial invariance recovers the earlier
Hilbert--Schmidt congestion estimate.  The operator-order statement is
an algebraic strengthening, but its endpoint symmetrization need not be
covariant under the raw presentation.  Therefore it is not, by itself, a
license for a reducing physical cut; the downstream Green-edge proof uses
its normalized trace consequence.
