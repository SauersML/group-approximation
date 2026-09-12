---
rg: 2
id: authenticated-mixed-loop-quartic-module-proof
kind: route
title: Cover every odd characteristic with five quartic stacked minors
target: authenticated-mixed-loop-kills-quartic-affine-modules
requires:
  - authenticated-mixed-loop-kills-cubic-affine-modules
---

Order the fifteen monomials of degree four lexicographically as

```text
x^4,x^3y,x^3z,x^2y^2,x^2yz,x^2z^2,
xy^3,xy^2z,xyz^2,xz^3,
y^4,y^3z,y^2z^2,yz^3,z^4.                              (QTP1)
```

Let `X_4,Y_4` be the matrices obtained by applying the substitutions
`(QMP2)` and `(QMP7)` to the universal rows `(MMP3)` on this basis.  Number
the output rows of `X_4` by `0,...,14` and those of `Y_4` by `15,...,29`.
All minors below use every input column in the order `(QTP1)`.

Direct expansion gives a full minor of the stacked matrix

```text
[X_4]
[Y_4]
```

on rows

```text
10,1,11,5,4,12,6,7,8,13,14,16,18,25,26               (QTP2)
```

with determinant

```text
-226809/65536
 =-(3^2*11*29*79)/2^16.                                (QTP3)
```

Thus the common kernel is zero in every odd characteristic except possibly
`3,11,29,79`.  The following four row sets give complementary full minors:

```text
characteristic 3:
  0,1,2,3,5,6,10,11,12,13,14,16,18,25,26,
  determinant 40843/4096;

characteristic 11:
  0,1,2,3,4,5,10,11,12,13,14,16,18,25,27,
  determinant 6399/256;

characteristic 29:
  0,1,2,3,4,5,10,11,12,13,14,16,18,25,26,
  determinant -7821/512;

characteristic 79:
  0,1,2,3,4,5,10,11,12,13,14,16,19,25,26,
  determinant -21483/256.                              (QTP4)
```

The four numerators in `(QTP4)` are respectively congruent to

```text
1 mod 3,        8 mod 11,        -20 mod 29,
5 mod 79,                                               (QTP5)
```

up to the immaterial displayed signs.  Hence the appropriate minor is
invertible in each exceptional characteristic.  Equations `(QTP3)--(QTP5)`
prove that the stacked operator has rank fifteen over every odd field, which
is exactly the zero-common-kernel assertion `(QTA1)`.

Every entry in the five fixed matrices comes from the prime-field
substitutions `(QMP2)` and `(QMP7)`, so the same certificates apply to every
Frobenius twist.  Filtration closure follows from `(MMP11)`.
