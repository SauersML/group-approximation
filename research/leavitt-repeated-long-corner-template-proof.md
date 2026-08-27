---
rg: 2
id: leavitt-repeated-long-corner-template-proof
kind: route
title: Pivot once and use the same long corner in both transport equations
target: leavitt-repeated-long-corner-template-kills-omega
requires:
  - leavitt-omega-has-an-explicit-distorted-target
  - leavitt-two-relator-corner-peeling
---

For coefficient slots `g_0,...,g_7` and signs `++-++-++`, the four orbit
relators have corner form

```text
H z,
z g_{5,0} z^(-1) g_{6,3} z L,
z g_{2,0} z^(-1) g_{3,3} z N,
z K.                                                   (RL1)
```

Set

```text
g_2=a,   g_3=c,   g_5=b,   g_6=d.                    (RL2)
```

The first relation gives `z=H^(-1)`.  If `L=N=H` already in the coefficient
corner subgroup, the middle equations reduce to

```text
H^(-1)bH d=1,        H^(-1)aH c=1.                  (RL3)
```

All four gates are involutions, so `(RL3)` is exactly
`d=H^(-1)bH` and `c=H^(-1)aH`.  It follows that

```text
[c,d]=H^(-1)[a,b]H=1.                               (RL4)
```

The fourth relation merely solves the independent corner `K` as `H`; it
does not affect `(RL4)`.  In the actual Leavitt packet `[a,b]=1`, whereas
`[c,d]=x_15(s_0^2)` is nonidentity.  Thus a full-support cyclic realization
of the repeated-tail equality is a Kervaire--Laudenbach violation.

The topology itself admits a literal repeated-tail collision: with formal
slots

```text
(x,x,1,1,x,1,1,x)
```

all four long corners reduce to `x_0x_1x_2x_3`.  Here the short gates are
identities, so this is only the incidence seed; the Leavitt-specific task is
to decorate the four identity slots by `(a,c,b,d)` while repairing the long
equalities with compound values in the remaining slots.
