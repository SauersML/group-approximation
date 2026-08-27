---
rg: 2
id: atlas-square-root-frame-has-unit-packet-residual
kind: claim
title: One H18 packet edge is a unit residual on the entire q14 square-root frame
artifacts:
  - experiments/atlas_a4_19243_component_localization.py
distinct_from:
  atlas-square-root-collision-constant-term-is-zero: that computes collision at the identity frame; this finds a packet word whose residual is a fixed nonzero transvection on the whole two-matrix frame.
  atlas-two-matrix-bezout-rank-gap-criterion: that gives the conditional consequence of any finite certificate; this supplies the certificate with one scalar entry equal to one.
  atlas-a4-packet-biclique-decomposition: that identifies the abstract K2,4 component; this uses its explicit natural matrices in the q14-adapted triangular gauge.
---

ESTABLISHED.  For every `s` and every `X,Y in M_s(F2)`, the q14-exact
triangular chart

```text
T=I+E13 tensor X+E14 tensor Y                         (UPR1)
```

has one of the twelve packet residuals equal, up to conjugacy by `T`, to

```text
(b a)^3-I=b-I,                                       (UPR2)
```

where `b-I` is a rank-one natural transvection.  Hence

```text
rank(w(T)-I)=s.                                       (UPR3)
```

The same statement holds after adding the square-root cyclic bridge
`E24 tensor R`, because that bridge also commutes with `b`.  Consequently
the square-root bridge construction can never make the packet residuals
`o(s)` before amplification or `o(s^2)` after `k=s` amplification.

Equivalently, the two-matrix algebra

```text
B=F2<x,y>/<entries of all thirteen P_w>
```

from `atlas-two-matrix-bezout-rank-gap-criterion` is the zero algebra.  One
matrix entry of the displayed packet residual is the constant polynomial
`1`, so the noncommutative Bezout certificate has length one.

### Coordinate proof

In the literal natural basis the marked q14 transvection has nilpotent part
`E34`.  Pass to the q14-adapted ordered basis

```text
(e1,e3,e4,e2),                                       (UPR4)
```

in which it becomes `E23` and `(UPR1)` is the triangular centralizer frame
used in `atlas-q14-exact-allows-full-coefficient-cyclicity`.

The large packet component is `H18=S3 x C3`.  Among its explicit labels are

```text
b=I+E12
```

in the literal basis and an order-three element `a` supported on the
disjoint `(e3,e4)` plane.  They commute and `a^3=1`, so

```text
(ba)^3=b.                                             (UPR5)
```

The `K_(2,4)` biclique contains their packet edge.  Under `(UPR4)`, `b-I`
becomes `E14`.  Every one of `E13,E14,E24` commutes with `E14`; therefore
both the unbridged chart `(UPR1)` and its `E24 tensor R` bridge commute with
`b`.

If the packet orientation is `(b_2 a_1)^3`, its value is directly
`(ba)^3=b`.  If its orientation is `(b_1 a_2)^3`, then

```text
b T a T^(-1)=T b a T^(-1),
```

so cubing gives `T(ba)^3T^(-1)=TbT^(-1)=b`.  Thus orientation does not
matter.  Finally `rank((b-I) tensor I_s)=s`, proving `(UPR3)`.  Since
`b-I=E14` has a scalar entry equal to one, the claimed length-one ideal
certificate follows.
