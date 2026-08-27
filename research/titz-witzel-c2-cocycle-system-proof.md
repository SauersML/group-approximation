---
rg: 2
id: titz-witzel-c2-cocycle-system-proof
kind: route
title: Evaluate the involution-sandwich presentation in the imprimitive wreath product
target: titz-witzel-c2-cocycle-system
requires:
  - titz-witzel-two-generator-involution-sandwich-normal-form
  - titz-witzel-central-square-lifts-collapse-mark
---

The action formula in `(TWC1)` gives the multiplication rule there directly.
In particular

```text
[A0,A1]_1^(-1)=[A1^(-1),A0^(-1)]_1.                      (1)
```

Starting with `(TWC2)`, apply this multiplication rule successively to every
definition in `(TW2G1)`.  The square of `u` is `[V0,V1]_0`.  Conjugating the
bare flip by `u` gives `[H0,H1]_1`, conjugating once more by the bare flip
interchanges its components, and hence gives `[A0,A1]_1`.  The next five
definitions give

```text
x=[A0 V1,A1 V0]_1,
c=[V0 A0 V1,V1 A1 V0]_1,
f=[X1^(-1) H1 X0,X0^(-1) H0 X1]_1,
d=[A0^(-1) F0,A1^(-1) F1]_1,
s=[F0 A1 F0,F1 A0 F1]_1.                                 (2)
```

Applying (1) three times to `rho=x^(-1)s^(-1)c^(-1)` gives the two `R`
words in `(TWC3)`.  Finally

```text
rho e rho^(-1)=[R0 R1^(-1),R1 R0^(-1)]_1
```

and multiplying this flip by `a` gives `[T0,T1]_0`.  This proves
`(TWC3)--(TWC4)`.

The same multiplication rule now evaluates the four even relators and gives
`(TWC5)` without an approximation.  The first line says that `c` is an
involution exactly when `C1=C0^(-1)`.  Under that equation, the last line is
equivalent to the final two equations of `(TWC7)`; the middle two lines give
the other four equations.  This proves `(TWC7)`.  Repeated squaring gives
`(TWC6)`.

For `(TWC8)`, put

```text
alpha=d_X(R0 R1,P),              beta=d_X(R1 R0,Q).
```

By `(TWC5)`, `delta_0=(alpha+beta)/2`.  Bi-invariance gives

```text
d_X(Q,R0^(-1) P R0)
 <= d_X(Q,R1 R0)+d_X(R1 R0,R0^(-1) P R0)
 = beta+alpha=2 delta_0.                                  (3)
```

The two components in `(TWC6)` are conjugate because
`Q P=P^(-1)(P Q)P`; hence the first equality in `(TWC9)`.  Moreover

```text
d_Omega(u e,e u)=d_X(P,Q),
d_Omega(u^2 e,e u^2)=d_X(P Q,Q P).                       (4)
```

For the first inequality, write `h=u e u^(-1)`, `a=e h e`, and
`c=u^2 a u^2`.  If `kappa=d_Omega(h,e)`, then bi-invariance gives
`d_Omega(a,e)=kappa` and telescoping gives
`d_Omega(u^4 e u^(-4),e)<=4 kappa`.  Cancelling the common outer powers
of `u` and changing the two occurrences of `a` to `e` therefore gives

```text
d_Omega(c^2,u^8)<=6 kappa.                               (5)
```

The first identity in (4) identifies `kappa` with `d_X(P,Q)`, and the
triangle inequality with the `c^2` defect proves the first inequality.
Substituting the second identity in (4) into
`titz-witzel-central-square-lifts-collapse-mark` proves the second one.

The attached checker independently evaluates the free words in the wreath
product, verifies every component formula in `(TWC3)--(TWC6)`, and tests the
metric identities on random finite permutations.
