---
rg: 2
id: qutrit-two-scalar-routers-leave-head-packet-finite
kind: claim
title: Two scalar routers close the full Leavitt host but every scalar-head return remains finite
artifacts:
  - research/qutrit-two-scalar-router-full-closure-proof.md
distinct_from:
  qutrit-head-preserving-scalar-router-is-three-cycle: that gives the support-minimal complete arrow and its local finite envelope; this adds a head-touching actor which reaches every scalar coordinate and computes the resulting full ambient subgroup.
  qutrit-head-only-overlap-envelope-is-finite: that proves finiteness after the whole scalar group is already present; this gives two explicit permutations, their qutrit intersections, the first returned head commutator, and the precise full-Leavitt generation threshold.
  qutrit-two-mixed-cells-are-rf-three-are-full-leavitt: that reaches an active EL4 core through three coefficient cells; this spreads that core to all 28 coordinates with one literal scalar cycle.
---

Retain the head-preserving router

```text
g_1=(c_0 d_0 d_1)
```

from `(QSA2)`. Choose two unused trivial coordinates `u_0,u_1` and list
the remaining scalar basis coordinates as `r_1,...,r_20`. Define the
head-touching 28-cycle

```text
g_2=(c_0 c_1 c_2 c_3 d_0 u_0 d_1 u_1
     r_1 ... r_20).                                     (QSR1)
```

The order is chosen so that `d_i` immediately precedes `u_i`. Then

```text
C intersect g_i C g_i^(-1)={1},             i=1,2,       (QSR2)
```

so both actors have the complete nine-character table

```text
||e_b g_i e_a||_2^2=1/81                  for all a,b.   (QSR3)
```

The second actor touches the head. With `Q_0=1-s_0t_0`,

```text
H_0=x_(c_2,c_1)(Q_0),
H_1=g_2H_0g_2^(-1)=x_(c_3,c_2)(Q_0),
B=[H_1,H_0]=x_(c_3,c_1)(Q_0).                           (QSR4)
```

Thus `<H_0,H_1>` is an exact `D_8` and `(QSR4)` is the first
literal head-touching `Q_0` return.

The ambient subgroup now closes completely:

```text
Gamma=<G_3,C,g_1,g_2>=EL_28(L_(F_2)(1,2)).              (QSR5)
```

Indeed `G_3` supplies `GL_4(F_2)` and all Leavitt coefficient roots on
the active four coordinates. Conjugating a bidirected active edge around
the 28-cycle gives every bidirected cycle edge, hence every scalar root.
Those scalar roots spread the four coefficient generators to every root
position.

Consequently `Gamma` is finitely presented, minimally almost periodic,
and nonsofic by the established Leavitt theorems. In every
finite-dimensional unitary representation the returned heads in
`(QSR4)` vanish together with the rest of `Gamma`. Its hyperlinearity is
not decided here.

There is nevertheless no new Hall gap. Put `E=(1-H_0)/2` and
`R=e_0+e_1`. The first router still has

```text
A=e_2g_1ER,
||A||_2^2=1/81,        tau(ER)=1/9,        tau(Ee_2)=1/18. (QSR6)
```

The second actor and every head word it returns remain in the finite
scalar-head envelope

```text
Lambda=<C,g_1,g_2,H_0>
       <=EL_28(F_2[Q_0])
       isomorphic to GL_28(F_2) times GL_28(F_2).         (QSR7)
```

The regular representation of `Lambda` realizes `(QSR2)--(QSR4)` and
`(QSR6)` exactly. Thus the new `D_8` return does not authenticate the
missing half of the source polar.

In fact `(QSR7)` is a general firewall: adjoining any finite family of
scalar matrices and any finite family of scalar conjugates or Steinberg
commutators of `Q_0`-roots never leaves the two-element coefficient
algebra `F_2[Q_0]`. No all-scalar routing network can by itself obstruct
microstates.

The exact next object must contain a raw `s_r` or `t_r` coefficient in
the same relation that claims to fill the missing source of `A`. Merely
closing all scalar coordinates, even though it already makes the ambient
group the full finitely presented nonsofic Leavitt group, leaves the
hyperlinearity problem open.
