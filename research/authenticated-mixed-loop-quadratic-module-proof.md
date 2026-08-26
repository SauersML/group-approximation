---
rg: 2
id: authenticated-mixed-loop-quadratic-module-proof
kind: route
title: Solve the two Fox rows on quadratic forms
target: authenticated-mixed-loop-kills-quadratic-affine-modules
requires:
  - authenticated-mixed-loop-kills-minuscule-affine-modules
---

Let `x,y,z` denote the standard basis vectors and write a general vector of
the symmetric square as

```text
P=A x^2+B xy+C xz+D y^2+E yz+F z^2.                   (QMP1)
```

Use the two universal rows `X,Y` from `(MMP3)`.  On the defining module the
relevant substitutions are

```text
q: x |-> x-(1/2)y,       s: y |-> y-(1/2)z,
A_0=x_12(2): y |-> y+2x,
B_0=d_12x_23(2): (x,y,z) |-> (2x,(1/2)y,z+y).          (QMP2)
```

Here `A_0,B_0` distinguish the group elements from the coefficients in
`(QMP1)`.  Expanding

```text
X P=A_0(P-qP)+B_0(P-sP)-P                              (QMP3)
```

and comparing the six monomial coefficients gives

```text
B=C=0,
A=-3D+2E,                    F=-(1/4)D+(1/2)E.         (QMP4)
```

For completeness, the two summands in `(QMP3)` have coefficient tables

```text
A_0(P-qP):
 x^2 A+2B,  xy 2B,  y^2 -A/4+B/2,  xz C,  yz C/2;

B_0(P-sP):
 xy B,  xz B,  y^2 D/4+E/2,  yz E,  z^2 -D/4+E/2.     (QMP5)
```

Now assume `(QMP4)`.  Then

```text
(1-q)P=A(xy-(1/4)y^2).                                 (QMP6)
```

The element

```text
u=q x_13(1)q^(-1)=1+E_13-(1/2)E_23                    (QMP7)
```

fixes both `x` and `y`, so the first term `(1-u)(1-q)P` in `YP` vanishes.
For `r=x_23(-1)` one has `r:z |-> z-y`, while
`h^(-1):(x,y,z)|->((1/2)x,y,2z)`.  Hence

```text
Y P=(E-F)y^2+4F yz.                                    (QMP8)
```

Because the characteristic is odd, `(QMP8)=0` implies `F=E=0`.
The last equation of `(QMP4)` then implies `D=0`, and the remaining equation
implies `A=0`.  Thus `P=0`, proving the common-kernel assertion.

Frobenius fixes the prime-field constants in the calculation.  Equation
`(QAM2)` and the contragredient calculation from the required claim give the
tensor-square statement.  Finally, the extension-closure argument
`(MMP11)` applies unchanged to any filtration with the stated sections.
