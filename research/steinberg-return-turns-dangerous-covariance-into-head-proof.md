---
rg: 2
id: steinberg-return-turns-dangerous-covariance-into-head-proof
kind: route
title: The nonzero covariance descendant returns to the head in one step
target: two-raw-unweighted-covariance-kills-jacobson-head
requires:
  - two-raw-roots-have-a-uniform-full-carrier-gap
---

From `TS=1`,

```text
QS=(1-ST)S=S-S(TS)=0,
TQ=T-TST=T-(TS)T=0.
```

Multiplication by the inverse pair also gives

```text
QTS=Q,                     TSQ=Q.                       (SRT1)
```

To see that the two opposite descendants do not vanish, use the faithful
half-line representation with

```text
S e_j=e_(j+1),
T e_0=0,                  T e_j=e_(j-1) for j>=1.
```

Then

```text
Q=E_(0,0),        QT=E_(0,1),        SQ=E_(1,0).        (SRT2)
```

In particular `QT` and `SQ` are nonzero ring elements.

For distinct root indices the characteristic-two Steinberg identity is

```text
[x_ij(a),x_jk(b)]=x_ik(ab).                             (SRT3)
```

Apply `(SRT3)` with `a=Q` and first `b=S`, then `b=T`.
Equations `(TRC1)--(TRC2)` give `(TRC3)--(TRC4)`.

Now pass to the quotient in which the dangerous covariance relation is
imposed. It says

```text
x_13(QT)=1.
```

Using a fourth index and `(SRT3)` again,

```text
1=[x_13(QT),x_34(S)]
  =x_14(QTS)
  =x_14(Q)                                                (SRT4)
```

by `(SRT1)`. A constant permutation matrix conjugates the ordered pair
`(1,4)` to `(1,2)`, so `x_12(Q)=h` is also one. This proves the quotient
collapse.

For the left-handed version, use root positions
`x_31(T),x_12(Q)` to obtain the harmless product `TQ=0`. The opposite
raw letter produces `SQ`; composing it on the left with `T` returns
`TSQ=Q` and repeats `(SRT4)`.

Finally, a root `x_13(QT)` is nonidentity because root subgroups are
copies of the additive ring and `QT!=0` by `(SRT2)`. In the left regular
representation of the elementary group,

```text
tau(lambda(x_13(QT)))=0,
||lambda(x_13(QT))-I||_2^2=2.                           (SRT5)
```

Thus the dangerous added relator has the exact defect floor claimed in the
marked infinite model. The obstruction is not a poor stability modulus:
the desired covariance equation contradicts the payload algebraically.
