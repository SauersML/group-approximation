---
rg: 2
id: qutrit-two-branch-sign-polar-has-hidden-half-absorber
kind: claim
title: The literal second Leavitt branch cuts the selected qutrit polar by a hidden sign
artifacts:
  - research/qutrit-two-branch-sign-polar-hidden-half-proof.md
distinct_from:
  jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16: that computes the four Q/QT sign-polar ranks; this adjoins the literal complementary letters s_1,t_1 and recomputes the surviving source.
  qutrit-parallel-full-cuntz-cell-covariance-is-finite: that gives a finite model for parallel Cuntz cells; this attaches both inverse branches to the named Jacobson sign polar and gives its exact rank table.
  jacobson-head-corner-radical-to-full-leavitt-corner: that proves q=s_1t_1 is a full Leavitt corner; this shows why the corresponding bounded group packet still does not authenticate two full-domain ranges.
---

Put `q=s_1t_1=1-s_0t_0` and, on the coordinate chain
`c_2 -> c_1 -> c_0 -> c_3`, define

```text
H=x_(c_2,c_1)(q),
U_r=x_(c_1,c_0)(t_r),          V_r=x_(c_0,c_3)(s_r),
A_r=[H,U_r]=x_(c_2,c_0)(qt_r),
W=x_(c_2,c_3)(q),              r=0,1.                  (QBH1)
```

The two literal inverse branches satisfy

```text
[U_r,V_s]=x_(c_1,c_3)(delta_(rs)),
[A_r,V_s]=W^(delta_(rs)).                               (QBH2)
```

Let

```text
E=(1-H)/2,
G_(sigma,tau)=E(1+sigma A_0)(1+tau W)/4,
P_sigma=G_(sigma,+)(1+A_1)/2.                           (QBH3)
```

Compress each branch successively by the selected sign projection. The
exact polar-support table is

| selected sign `(sigma,tau)` | `t_0,s_0` branch | `t_1,s_1` branch |
|---|---:|---:|
| `(+,+)` | `G_(+,+)` | `P_+` |
| `(-,+)` | `0` | `P_-` |
| `(+,-)` | `0` | `0` |
| `(-,-)` | `0` | `0` |

More explicitly,

```text
(G_(sigma,tau) U_0 G_(sigma,tau))^2
 =G_(sigma,tau)  if sigma=+, and 0 if sigma=-,

(G_(sigma,tau) U_1 G_(sigma,tau))^2
 =G_(sigma,tau)(1+A_1)/2,

(P_sigma V_1 P_sigma)^2=P_sigma,                        (QBH4)
```

in the surviving `tau=+` row; the last square is zero when `tau=-`.
The analogous `V_0` compression survives exactly when `tau=+`.

Thus the second branch is not a second full-domain copy of the selected
polar. It introduces the independent hidden sign `A_1=+1`. On the
qutrit source cut `R=e_0+e_1`, the exact polar ranks are

```text
tau(supp|G_(+,+)R|)=5/72,
tau(supp|P_+R|)=11/288,

tau(supp|G_(-,+)R|)=1/16,
tau(supp|P_-R|)=7/192.                                  (QBH5)
```

The proposed target has `tau(Ee_2)=1/18`. Hence

```text
11/288 < 1/18,                 7/192 < 1/18.            (QBH6)
```

Only the original `(+,+)` branch retains a source larger than the target,
by `1/72`. The literal complementary branch supplies no second capacity
violation; its source is nested in the original source and already fits
inside the target.

This failure has an exact finite absorber. Before adjoining the qutrit
torus, the five roots `H,U_0,U_1,V_0,V_1` generate

```text
1+mathcal N,                  dim_(F_2)(mathcal N)=9,
|1+mathcal N|=2^9,           mathcal N^4=0.             (QBH7)
```

Adjoining `C` and the minimal router `g_1` still preserves the four-stage
acyclic flag and gives a finite group. Its regular representation retains
`H`, both literal Leavitt branches, all four qutrit sign polars, and the
ranks in `(QBH5)` exactly.

Therefore the bare two-branch/full-corner relation is absorbed. A viable
continuation must put the long router `g_2` in the same operator which
preserves the original `5/72` source and forces its range into `Ee_2`.
Routing a separately constructed `s_1,t_1` return cannot add the missing
capacity.
