---
rg: 2
id: iwahori-symmetric-two-cubic-torsion-retraction-proof
kind: route
title: Reconstruct the square-free core from two independently rounded triangle products
target: iwahori-symmetric-two-cubic-torsion-retraction
requires:
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
  - even-weil-second-cubic-has-a-rank-six-determinant-gap
---

The identities `(STR5)` follow directly from `X^2=1`:

```text
XT_1=X^2A=A,
XT_1^2R_1=XT_1^2T_1^(-2)XB=B.
```

Also `T=XA_old`, so the first estimate in `(STR6)` is immediate.  From
`B_old=XT^2R` one has

```text
R=T^(-2)XB_old.                                      (STP1)
```

Telescoping `(STR4)` against `(STP1)`, and using

```text
rank(T_1^(-2)-T^(-2))<=2 rank(T_1-T),                (STP2)
```

gives the second estimate in `(STR6)`.

The old inversion row in `(STR1)` says `(XR)^2=1`.  A word telescoping
between `(XR_1)^2` and `(XR)^2` uses `R_1-R` twice, hence

```text
rank(u-1)<=2 rank(R_1-R)<=4r_A+2r_B.                 (STP3)
```

Likewise compare `v` with the old exact BS word
`RTR^(-1)T^(-4)=1`.  The two occurrences of `R` cost
`2(2r_A+r_B)` and the five occurrences of `T` cost `5r_A`.  This is
`9r_A+2r_B`, proving `(STR8)`.

For determinants, cancellation in the BS commutator gives

```text
det(v)=det(T_1)^(-3).
```

Since `T_1=XA`, `X^2=1`, and `A^3=1`, this equals `det(X)`.  Further,

```text
det(R_1)=det(T_1)^(-2)det(X)det(B)
        =det(A)det(X)det(B),                          (STP4)
```

because `det(X)^2=1` and `det(A)^3=1`.  Consequently

```text
det(u)=det(XR_1)^2=(det(A)det(B))^2,
```

which is a cube root of unity.  The even-Weil rank inputs are exactly the
rank-two first-cubic spectrum and the rank-six second-cubic residual from
the two required claims, giving `(STR10)`.
