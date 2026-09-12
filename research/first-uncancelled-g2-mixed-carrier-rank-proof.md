---
rg: 2
id: first-uncancelled-g2-mixed-carrier-rank-proof
kind: route
title: Conjugate both sign roots through the raw S/T carrier
target: first-uncancelled-g2-mixed-carrier-has-no-hall-deficit
requires:
  - first-g2-mixed-return-has-a-dihedral-half-absorber
  - qutrit-two-branch-sign-polar-has-hidden-half-absorber
---

## 1. Keep the raw entries uncollected

Write `U=U_2=x_(c_3,c_2)(T)` in this proof. Direct matrix
multiplication along `c_2 -> c_3 -> c_0` gives

```text
VU=I+S E_(c_0,c_3)+T E_(c_3,c_2)+ST E_(c_0,c_2).
                                                               (UGM5)
```

Thus both raw entries remain visible. The final term is the root `P`
from the preceding theorem, and

```text
[V,U]=P,                       (VU)^2=P.                 (UGM6)
```

The two relevant sign conjugations are

```text
VAV=AW,                        UWU=WZ.                  (UGM7)
```

The first identity is the matched branch relation `qTS=q`. For the
second, use the `(c_3,c_2)` corner

```text
U=[[1,T],[0,1]],               W=[[1,0],[q,1]].
```

Since `Tq=0` and `qT=a`,

```text
(UW)^2=[[1,0],[0,1+a]]=Z,
```

which is equivalent to the second identity in `(UGM7)`. The elements
`U` and `V` fix `H,Z`; moreover `U` fixes `A` and `V` fixes `W`.

## 2. Exact initial support

Let `Y=VU`. Since `Y^(-1)=UV`, equations `(UGM7)` give

```text
Y^(-1)AY=AWZ,                    Y^(-1)WY=WZ.           (UGM8)
```

All involutions on the right commute. Put

```text
X=G_(sigma,tau)Y G_(sigma,tau).
```

Then

```text
X^*X
 =G_(sigma,tau)(Y^(-1)G_(sigma,tau)Y)G_(sigma,tau).
                                                               (UGM9)
```

On the outer `G_(sigma,tau)` carrier, `A=sigma` and `W=tau`.
The conjugated `A=sigma` condition in `(UGM8)` becomes

```text
sigma*tau*Z=sigma,              equivalently Z=tau.
```

The conjugated `W=tau` condition becomes

```text
tau*Z=tau,                      equivalently Z=+1.
```

These two Fourier cuts agree when `tau=+` and are orthogonal when
`tau=-`. Therefore

```text
X^*X=G_(sigma,+)(1+Z)/2        if tau=+,
X^*X=0                         if tau=-.                (UGM10)
```

This proves `(UGM2)`. It also proves that `X` is a partial isometry,
so no functional-calculus approximation is hidden in the argument.

For the reverse carrier `Y'=UV=Y^(-1)`, direct conjugation gives

```text
YAY^(-1)=AW,                    YWY^(-1)=WZ.
```

The first outer sign then requires `tau=+` and the second requires
`Z=+`. Hence `G Y' G` has the same support `(UGM10)`.

## 3. Insert the qutrit source and target cuts

For `tau=+`, equation `(UGM10)` identifies the initial projection with
the projection `K_(sigma,+)` in the preceding exact rank theorem.
Therefore

```text
tau(supp abs(G_(+,+)Y G_(+,+)R))=43/1152,
tau(supp abs(G_(-,+)Y G_(-,+)R))=7/192.                (UGM11)
```

The same holds for `Y^(-1)`, while both negative-`tau` rows vanish.

Now set

```text
L_b=Ee_b g_2,                  T_b=L_b X R.
```

The operator `L_b` is a contraction and its range is contained in
`Ee_b`. If `v` lies in the kernel of `(XR)^*(XR)`, then `XRv=0`,
hence also `L_bXRv=0`. Thus

```text
supp abs(T_b) <= supp abs(XR)                            (UGM12)
```

as initial projections. This proves the rank inequalities `(UGM4)`.
The target projection has trace

```text
tau(Ee_b)=1/18=64/1152.
```

Both positive-`tau` upper bounds, `43/1152` and
`7/192=42/1152`, already fit. Any additional loss caused by the target
compression only makes the inequality stricter.

Expanded inside `(UGM3)`, the carrier is

```text
Ee_b g_2 G V g_2^2 U g_2^(-2) G R.
```

It therefore contains a target `g_2` leg which does not cancel and the
literal raw `S` and `T` entries in the same operator. The failure is
structural: the two sign transports share the same dihedral involution
`Z`, so their overlap selects one hidden half rather than restoring the
full source.
