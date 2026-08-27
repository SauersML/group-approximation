---
rg: 2
id: binary-jacobson-naive-head-polar-proof
kind: route
title: Factor the balanced shift and compute both supports of its head compression
target: binary-jacobson-naive-head-polar-is-balanced-return
requires:
  - binary-jacobson-constant-q-root-envelope-is-finite
---

The factorization and involution calculation are the ones used in
`binary-jacobson-active-cycle-generation-proof`:

```text
h=a w_12=[[Q,S],[T,0]],
h^2=[[Q^2+ST,QS],[TQ,TS]]=1.                             (1)
```

Conjugating a column root with target outside the first two coordinates
left-multiplies its coefficient column by this two-by-two block.  For
`w=x_13(Q)`, the column is `(Q,0)^t`, and

```text
[[Q,S],[T,0]] (Q,0)^t=(Q^2,TQ)^t=(Q,0)^t.               (2)
```

This proves `(JNP2)`.  The same calculation with target `4` proves
`Ad(h)x_14(Q)=x_14(Q)`.  The root `x_43(1)` uses neither row nor column
`1,2`, so it commutes with `h`; this proves `(JNP4)`.

Since `P` is a polynomial in `rho(w)`, `(JNP2)` gives `[P,rho(h)]=0`.
Using `a=hu` yields `(JNP5)`.  The constant Weyl swap moves row `1` to row
`2`, so

```text
u x_13(Q)u^(-1)=x_23(Q).                                 (3)
```

The two roots in `(3)` share one target and commute.  Therefore their
negative spectral cuts `P,P'` commute.  With `u=u^*=u^(-1)`,

```text
R^*R
 =P rho(u)P rho(h)^*rho(h)P rho(u)P
 =P rho(u)P rho(u)P
 =P P'.                                                   (4)
```

For the final support, conjugating `x_23(Q)` by `h` left-multiplies the
coefficient column `(0,Q)^t`:

```text
[[Q,S],[T,0]] (0,Q)^t=(SQ,0)^t,
Ad(h)x_23(Q)=x_13(SQ).                                   (5)
```

Thus `P''=rho(h)P'rho(h)^*` is the negative cut of `x_13(SQ)`.  It commutes
with `P`, because same-position root elements commute.  Consequently

```text
RR^*=rho(h)P P'rho(h)^*=P P''.                           (6)
```

Equations `(4)` and `(6)` show that `R` is already a partial isometry and
prove `(JNP6)`.  Its initial and final projections are unitarily equivalent,
giving `(JNP7)`.  Notice that only the initial projection belongs entirely
to the finite constant/`Q` envelope; equation `(5)` is precisely where the
raw `S/T` information first enters.  The calculation therefore authenticates
a raw return while simultaneously showing that this one occurrence carries
no rank excess.
