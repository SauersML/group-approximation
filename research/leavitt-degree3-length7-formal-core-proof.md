---
rg: 2
id: leavitt-degree3-length7-formal-core-proof
kind: route
title: Exhaust the one-letter formal slots through length five and exhibit length seven
target: leavitt-degree3-length7-formal-core-exists
requires:
  - leavitt-two-relator-corner-peeling
---

The artifact enumerates every exponent-three sign word at lengths three,
five, and seven and every slot assignment from `{1,x,x^(-1)}`.  It computes
the Reidemeister--Schreier orbit corners and reduces exactly in

```text
<x_0>*<x_1>*<x_2>.
```

It accepts only when two nontrivial unary words occur, up to inversion, in
two distinct corners of a non-unary orbit.  There is no hit at lengths three
or five.  The first length-seven hit is the displayed word, whose reduced
orbits are

```text
orbit 0: (-,x_2), (+,x_0 x_1), (+,x_0^-1),
         (-,x_2^-1), (+,1)
orbit 1: (+,x_2)
orbit 2: (+,x_0).
```

The two unary corners therefore recur in distinct target corners, proving
the claimed nonempty incidence core and the stated minimality within the
one-letter formal slot alphabet.
