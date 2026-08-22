---
rg: 2
id: atlas-a8-index-91-to-496-reaches-standard-l5
kind: claim
title: The first finite-simple A8 overgroup after index ninety is the standard subgroup class in L5(2)
artifacts:
  - experiments/atlas_a8_agl4_complement_classes.py
distinct_from:
  atlas-a8-index-33-to-89-is-orthogonal-sp6: that treats the preceding order interval and reduces it to one orthogonal Sp6(2) class; this treats the next interval and resolves the affine-complement ambiguity in the two L5(2) parabolics.
  atlas-a4-gl5-packet-collision-screen: that screens one relative labeling parity of the standard subgroup class; this proves every A8 subgroup in the sole surviving ambient group belongs to that class and identifies the untested opposite parity.
---

Let `S` be finite nonabelian simple and `A<S` with `A ~= A8`.  There is no
such pair with

```text
91 <= [S:A] < 496.                                  (SIL1)
```

At equality 496 one necessarily has

```text
S ~= L_5(2),       [S:A]=496,                       (SIL2)
```

and `A` is conjugate to the standard block-diagonal `GL_4(2)` subgroup of
`GL_5(2)`.

The standard subgroup is self-normalizing.  Consequently marked embeddings
have two relative label parities.  The same-parity family is exactly the
family killed by `atlas-a4-gl5-packet-collision-screen`.  The opposite-parity
family, in which one chart uses the natural four-dimensional module and the
other its dual, is the first exact finite-simple carrier not covered by the
existing screens.

This is CFSG/ATLAS-dependent.  The order interval uses the GAP Character
Table Library simple-order table.  The maximal subgroups of `U4(3)` and
`L5(2)` are those in the *Atlas of Finite Groups* and its verified online
tables.  The only extra calculation is the exact complement-class certificate
for `2^4:A8`.

