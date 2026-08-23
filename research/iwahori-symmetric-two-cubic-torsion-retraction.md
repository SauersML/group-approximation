---
rg: 2
id: iwahori-symmetric-two-cubic-torsion-retraction
kind: claim
title: Independent cubic rounding gives a smaller exact Iwahori torsion carrier
distinct_from:
  iwahori-two-triangle-torsion-normal-form: that normalizes an arbitrary approximate five-relator tuple sequentially and gives norm bounds; this exploits an already exact involution, inversion row and BS core to round the two original cubic products independently and retain sharper rank carriers.
  five-mod-eight-torsion-normalization-retains-a-padding-charge: that extracts a determinant charge after the sequential normalization; this supplies a smaller retraction on which either determinant or eigenangle charges can be computed.
---

Let `X,R,T` be unitaries satisfying

```text
X^2=1,       X R X=R^(-1),       R T R^(-1)=T^4.     (STR1)
```

Put

```text
A_old=XT,                   B_old=XT^2R.              (STR2)
```

Round these two unitaries independently by spectral calculus to
`A^3=B^3=1`, and suppose

```text
rank(A-A_old)<=r_A,         rank(B-B_old)<=r_B.       (STR3)
```

Define

```text
T_1=XA,                    R_1=T_1^(-2)XB.            (STR4)
```

Then `(X,A,B)` is an exact `C_2*C_3*C_3` torsion frame and reconstructs
the two triangle rows exactly:

```text
XT_1=A,                    XT_1^2R_1=B.               (STR5)
```

Moreover

```text
rank(T_1-T)<=r_A,
rank(R_1-R)<=2r_A+r_B.                               (STR6)
```

For the two structural words

```text
u=(XR_1)^2,
v=R_1T_1R_1^(-1)T_1^(-4),                            (STR7)
```

one has

```text
rank(u-1)<=4r_A+2r_B,
rank(v-1)<=9r_A+2r_B.                                (STR8)
```

Their determinant charges are

```text
det(u)=(det(A)det(B))^2 in mu_3,
det(v)=det(X) in {+1,-1}.                             (STR9)
```

For the compressed even-Weil boundary, `r_A<=2` and `r_B<=6`, so

```text
rank(u-1)<=20,              rank(v-1)<=30.            (STR10)
```

On the canonical `p=1 mod 8` neutral progression, the sharper carrier
calculation in `neutral-weil-symmetric-retraction-is-double-neutral` has
`r_A=r_B=2`.  Hence `(STR8)` improves there to

```text
rank(u-1)<=12,              rank(v-1)<=22,            (STR11)
det(u)=det(v)=1.
```

This does not by itself give a positive Frobenius floor when both
determinants in `(STR9)` are one.  It reduces that last neutral calculation
to a uniformly bounded carrier (at most thirty-four dimensions in the
canonical neutral progression), with no
sequentially generated rank-eighteen second-rounding sector.
