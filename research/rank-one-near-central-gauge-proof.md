---
rg: 2
id: rank-one-near-central-gauge-proof
kind: route
title: Extract the braid-block algebra and bound every near-central sheet gauge
target: rank-one-closure-reduces-to-noncentral-gauge
requires:
  - rank-one-conjugacy-kills-c2-congruence-fold
  - two-torus-closures-detect-denominator-multiplicity
---

Use the exact congruence matrices `e_12,e_23,b_21,b_32,w_12,w_23` and
`K=rho(h)` from `(CAP1)`.  On `K_sh tensor K_actor` set

```text
E_12=P tensor e_12,             B_21=Q tensor b_21,
E_23=R tensor e_23,             B_32=T tensor b_32.    (NCB1)
```

The two rank-one definitions give

```text
A_12=P^2 tensor a_12,           W_12=U tensor w_12,
A_23=R^2 tensor a_23,           W_23=V tensor w_23,
U=PQP,                          V=RTR.                 (NCB2)
```

Separating the exact actor tensor factor from the rank-one conjugacy and the
two closed returns gives exactly

```text
UPU^*=Q,
URU^*=[P,R]=V^*PV.                                    (NCB3)
```

The first equality and `U=PQP` imply the braid relation.  Indeed
`UP=QU`, so

```text
PQP^2=QPQP,
PQP=QPQ.                                              (NCB4)
```

All gauges commute with `S`; hence the spectral projections of `S` reduce
all of them and `(NCB2)--(NCB4)` split over `K_+ direct-sum K_-`.  No scalar
conclusion is possible from these equations alone.  Taking `P,R,Q,T` to be
the corresponding matrices of an exact nonabelian congruence representation
on either block gives an explicit noncommutative solution.

We now prove the quantitative assertion.  Choose the central unitaries in
`(NCG5)` and set

```text
U_0=P_0Q_0P_0,                V_0=R_0T_0R_0.
```

Unitary word telescoping gives

```text
||U-U_0||_2<=3 epsilon,       ||V-V_0||_2<=3 epsilon,
||[P,R]-1||_2<=4 epsilon.                              (NCB5)
```

Since the central approximants commute, the first closed return in `(NCB3)`
and `(NCB5)` imply

```text
||R_0-1||_2
 <=||U_0R_0U_0^*-URU^*||_2+||[P,R]-1||_2
 <=7 epsilon+4 epsilon=11 epsilon.                    (NCB6)
```

The second return gives the same estimate for `P_0`:

```text
||P_0-1||_2<=11 epsilon.                              (NCB7)
```

Finally the rank-one conjugacy gives

```text
||Q_0-P_0||_2<=8 epsilon.                             (NCB8)
```

Thus

```text
||P-1||_2<=12 epsilon,
||R-1||_2<=12 epsilon,
||Q-1||_2<=20 epsilon,                                (NCB9)

||U-1||_2<=44 epsilon,       ||V-T||_2<=24 epsilon.   (NCB10)
```

Write the sheet parts of the two torus closures as

```text
d_12=P^2GQG^*P^2U^*,
d_23=R^2GTG^*R^2V^*.                                  (NCB11)
```

Using `(NCB9)--(NCB10)` once more in fixed-word telescoping,

```text
||d_12-1||_2<=112 epsilon,
||d_23-GTG^*T^*||_2<=72 epsilon.                      (NCB12)
```

The exact congruence factors of `d_12,d_23` multiply to `K`.  Therefore
`(NCG6)` and `(NCB12)` yield

```text
||GTG^*T^*-G||_2<=eta+184 epsilon.                    (NCB13)
```

For every unitary `T` there is an exact identity

```text
||GTG^*T^*-G||_2
 =||TG^*T^*-1||_2
 =||G-1||_2.                                          (NCB14)
```

This proves the first line of `(NCG7)`.  Since the actor factor cancels from
the fold,

```text
F=GSG^*S,
||F-1||_2<=2||G-1||_2,
||F^2-1||_2<=2||F-1||_2.                              (NCB15)
```

The standard identity

```text
tr(Q_fP_fQ_f-(Q_fP_fQ_f)^2)=(1/32)||F^2-1||_2^2
```

then proves `(NCG8)`.
