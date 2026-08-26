---
rg: 2
id: authenticated-mixed-loop-cubic-module-proof
kind: route
title: Give complementary odd-characteristic minors on the cubic torus kernel
target: authenticated-mixed-loop-kills-cubic-affine-modules
requires:
  - authenticated-mixed-loop-kills-quadratic-affine-modules
---

Order the monomial basis of `Sym^3(K^3)` as

```text
x^3, x^2y, x^2z, xy^2, xyz, xz^2, y^3, y^2z, yz^2, z^3. (CMP1)
```

Use the substitutions `(QMP2)` in the universal torus row `X`.  Elementary
expansion gives the following ten nonzero coordinate rows, where `c_j`
denotes the coefficient of the `j`th monomial in `(CMP1)`:

```text
2c_1+4c_3,
2c_1+6c_3,
2c_1+2c_4,
-(1/2)c_1+(5/2)c_3+c_4,
3c_4,
-(1/2)c_3+c_4,
(1/8)c_0-(1/4)c_1+(1/2)c_3-(7/8)c_6
  +(1/4)c_7+(1/2)c_8,
-(1/4)c_2+(1/2)c_4-(3/4)c_7+(3/2)c_8,
(1/2)c_5-(1/4)c_7+(1/2)c_8,
(1/8)c_6-(1/4)c_7+(1/2)c_8-c_9.                  (CMP2)
```

The submatrix of `(CMP2)` in rows `0,1,2,6,7,8,9` and columns
`0,...,6` has determinant `1/64`.  Hence it has rank seven in every odd
characteristic.  Solving `(CMP2)=0` leaves the three free coefficients
`c_7,c_8,c_9`; equivalently, the torus kernel has basis

```text
v_7=12x^3-3x^2z+(1/2)xz^2+2y^3+y^2z,
v_8=-32x^3+6x^2z-xz^2-4y^3+yz^2,
v_9=56x^3+8y^3+z^3.                                  (CMP3)
```

The displayed determinant and direct substitution of `(CMP3)` into
`(CMP2)` prove that this is a basis over every odd-characteristic field, not
merely in characteristic zero.

Now apply the authenticated row `Y`.  Only four output coordinates are
needed.  Relative to the ordered kernel basis `(v_7,v_8,v_9)`, their
coefficient rows are

```text
x^2y: (2,-4,0),
y^3:  (21/16,-13/8,1),
y^2z: (1/4,7/2,-6),
yz^2: (0,0,12).                                      (CMP4)
```

The determinant of the rows `(x^2y,y^3,yz^2)` is `24`, while the determinant
of `(x^2y,y^3,y^2z)` is `-20`.  An odd prime cannot divide both numbers.
Therefore `(CMP4)` has rank three over every odd-characteristic field, and
`Y` kills no nonzero vector in `ker X`.  This proves `(CAM1)`.

All substitutions use only prime-field scalars, so Frobenius twists obey the
same calculation.  The filtration statement follows once again from the
extension-closure argument `(MMP11)`.
