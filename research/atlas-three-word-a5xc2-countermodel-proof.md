---
rg: 2
id: atlas-three-word-a5xc2-countermodel-proof
kind: route
title: A graph-D10 coset action makes both order-six restrictions regular
target: atlas-three-word-a5xc2-countermodel
requires:
  - atlas-three-word-c6-s3-core
---

All identities can be checked in `A5`.  With the cycle convention of the
claim,

```text
z=yx=x y x^-1,
(yr)^3=(z r^-1)^3=1.
```

After adjoining a central involution `c`, the collision relation reduces to

```text
x c y c x^-1 c z c
 = x y x^-1 z
 = z^2
 = 1.
```

It remains only to verify the regular margins.  The dihedral subgroup
`D10=<d,s>` has five rotations and five reflections.  Its graph subgroup
`L<G=A5 x C2` has order ten, hence `G/L` has twelve points.

A nonidentity element of `<r,c> ~= C6` cannot lie in any conjugate of `L`:
its possibilities have orders/central coordinates

```text
r,r^2       : order 3, central coordinate 0,
c            : A5 coordinate 1, central coordinate 1,
r c,r^2 c   : A5 order 3, central coordinate 1.
```

By contrast graph-`D10` elements are rotations of order `1` or `5` with
central coordinate zero, or double-transposition reflections with central
coordinate one.  Thus `<r,c>` acts freely on the twelve cosets.

Likewise every nonidentity element of `<x,y> ~= S3` has central coordinate
zero and order two or three.  Graph-`D10` has no order-three element, and its
order-two elements all have central coordinate one.  Hence this `S3` also acts
freely.

A free action of a six-element group on twelve points is the disjoint union of
two regular orbits.  Therefore the coset representation is simultaneously
`2 Reg(C6)` and `2 Reg(S3)` and realizes the exact core relations.  Applying
`atlas-three-word-c6-s3-core` embeds its amplifications into the regular-A8
three-word problem.
