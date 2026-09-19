---
rg: 2
id: iwahori-two-triangle-torsion-normal-form
kind: claim
title: Both Iwahori triangles exactify before the two structural rows
distinct_from:
  bs14-cubic-rounding-leaves-relative-core-basin: that rounds the two cubic products while holding the old BS coordinates fixed and therefore leaves a relative incidence problem; this deliberately changes the square-free coordinates so that both triangle relations become exact in one common tuple.
  iwahori-square-free-bs14-presentation: that eliminates the half-parabolic and identifies the five square-free relators; this is the quantitative same-dimensional normalization which makes the three torsion relators exact and moves all error into the remaining two structural relators.
  same-core-involution-cubic-gauge-coercivity: that controls a gauge after an exact extending core is known; this is a pre-basin normalization requiring no exact endpoint.
---

Use the square-free Iwahori coordinates `(X,R,T)` and suppose first that
`X^2=1`.  Put

```text
eta=||(XT)^3-1||_2,
zeta=||(XT^2R)^3-1||_2.
```

There are unitaries `T_1,R_1` in the **same dimension** such that

```text
(X T_1)^3=1,                 (X T_1^2 R_1)^3=1,       (TTN1)
||T_1-T||_2<=eta/2,
||R_1-R||_2<=(zeta+3eta)/2.                            (TTN2)
```

If the original structural defects are

```text
d_inv=||X R X-R^(-1)||_2,
d_BS =||R T R^(-1)-T^4||_2,
```

then the normalized tuple satisfies

```text
||X R_1 X-R_1^(-1)||_2 <=d_inv+zeta+3eta,             (TTN3)
||R_1T_1R_1^(-1)-T_1^4||_2
 <=d_BS+zeta+(11/2)eta.                               (TTN4)
```

Thus every vanishing-defect Iwahori sequence can first be put, at vanishing
cost, in a normal form where all three torsion rows

```text
X^2=1,             (XT)^3=1,             (XT^2R)^3=1
```

hold exactly and only the inversion and BS covariance rows remain
approximate.  If `X^2=1` is initially approximate, nearest-root spectral
rounding makes it exact first and changes every displayed bound only by a
universal constant multiple of `||X^2-1||_2`.

Equivalently, put

```text
A=XT,       B=XT^2R.
```

The exact torsion frame is a representation of `C_2*C_3*C_3`; conversely

```text
T=XA,       R=T^(-2)XB.                                (TTN5)
```

Hence the full Iwahori group C-star algebra is the quotient of the
torsion-frame algebra `C^*(C_2*C_3*C_3)` by just the two fixed structural
words obtained from BS covariance and inversion.  The explicit rounding
above makes all finite-order/triangle lifting automatic in the normalized-HS
matrix problem; no abstract C-star semiprojectivity assertion is needed.
A qualitative quotient-lifting proof must split those two structural rows
simultaneously.  Compactness or finite-spectrum rounding has no further work
to do.
