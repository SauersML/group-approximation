---
rg: 2
id: leavitt-d4-metacyclic-retraction-leak-proof
kind: route
title: Realize the projection equations in the affine group of Z mod 16
target: leavitt-d4-metacyclic-retraction-leak
requires: []
---

Let `w:x|->x+1` and `z:x|->13x+1` on `Z/16`, fixing four extra points.
As permutation units on the twenty-leaf Bergman chart they satisfy

```text
w^16=1,  z w z^-1=w^-3,  z^4=w^12,  w^8!=1.
```

Set

```text
a=1,  d=w,  c=wz,  b=w z^-1 w.
```

For `H=b_0c_1d_2a_3` and the three cyclic Latin rows

```text
B0=a_0b_1c_2d_3,
B1=d_0a_1b_2c_3,
B2=c_0d_1a_2b_3,
```

put `F=H^-1B0H^-1B1H^-1B2`.  Direct exact multiplication gives copy
retractions `(w^8,1,1,1)`, exactly the proposed terminal projection chain.
But reduction in the free product of the four coefficient copies leaves
sixteen nonidentity blocks.  In particular `F!=(w^8)_0`.

`research/artifacts/verify-degree4-metacyclic-retraction-leak.py` performs
the calculation with faithful partial-bijection normal forms and asserts
all displayed identities.  It additionally enumerates the six cyclic/inverse
orientations of each triangle face.  Eight of the 216 orientations link their
three carriers for the displayed gauge, but none has a one-copy nonidentity
coefficient boundary.  Finally it generates the complete 64-element packet
`<w,z>` and exhausts every free-gauge choice `b=k`, with

```text
x=w^2z,  a=kx,  d=aw,  c=dz.
```

No gauge and no orientation produces a one-copy nonidentity boundary.  This
is a countermodel to the inference from the four retractions and a complete
fence for this order-sixteen metacyclic packet, not for coefficient units
outside that packet.
