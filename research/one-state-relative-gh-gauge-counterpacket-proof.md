---
rg: 2
id: one-state-relative-gh-gauge-counterpacket-proof
kind: route
title: Fix one density column and flip its trace-large orthogonal complement
target: one-state-protected-coefficient-leaves-relative-gh-gauge
requires:
  - lin-state-dependent-gh-preserves-the-commutant
  - summed-reynolds-carrier-transports-only-tautologically
---

Every `I_L tensor Q` commutes with `(SPG1)`.  Hence multiplying a packet
comparison intertwiner by that unitary preserves its exact intertwining
equations.  For `(SPG2)`, `(Q_m-I)^*(Q_m-I)` is zero on `e_1` and equals
`4I` on `span(e_2,...,e_m)`.  Therefore

```text
Tr(rho_m (Q_m-I)^*(Q_m-I))=4(m-1)/m^3,
(1/m)Tr((Q_m-I)^*(Q_m-I))=4(m-1)/m,
```

which proves `(SPG3)` and `(SPG4)`.  Tensoring with normalized trace on `L`
does not change either value.  Replacing `rho_m` by the rank-one density on
`e_1` makes the first value zero.  This is an exact packet and exact
intertwiner construction; only the protected state norm tends to zero.

For `(SPG5)`, use unitary invariance twice:

```text
||Q_2 B Q_1^*-B||_2
 =||Q_2 B-BQ_1||_2
 =||Q_2-BQ_1B^*||_2.
```

Thus zero error gives `Q_2=BQ_1B^*`, and the same equality gives the
constant-one quantitative statement.

Finally, `(SPG6)` implies

```text
||X||_(2,rho)^2=Tr(rho X^*X)
 >=(c/m)Tr(X^*X)=c||X||_(2,tr)^2.
```

The smallest eigenvalue in `(SPG2)` is `m^(-3)`, so the best such `c` is
`m^(-2)` and no uniform promotion is possible.  Lin's `A'`-linearity remains
valid throughout the counterpacket because all multiplicity gauges commute
with the label packet; it does not choose one of them.  This proves both the
negative state-dependent assertion and the sharp full-unitary converse.
