---
rg: 2
id: neutral-weil-symmetric-retraction-is-double-neutral
kind: claim
title: The canonical neutral Weil torsion retraction is always double determinant neutral
distinct_from:
  one-mod-eight-torsion-charge-reduces-to-a-double-neutral-angle: that allows a possible nontrivial determinant of u for a general sequential torsion normalization; this proves that branch never occurs for the symmetric independent nearest-root retraction.
  five-mod-eight-torsion-normalization-retains-a-padding-charge: that obtains its energy floor from det v equals minus one; here both structural determinants are exactly one.
  even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two: that computes the relative position of the two pre-retraction residual carriers; this computes what scalar charges survive after both carriers are rounded away.
---

Let `p=1 mod 8` and start from the compressed even-Weil square-free tuple
`(X,R,T)`, for which inversion and BS covariance are exact.  Put

```text
A_old=XT,                    B_old=XT^2R.
```

Independently nearest-root round them to `A^3=B^3=1`, and define the
symmetric torsion retraction

```text
T_1=XA,                      R_1=T_1^(-2)XB.          (CNR1)
```

Then all three torsion rows are exact.  For the structural words `u,v` in
the resulting `C_2*C_3*C_3` frame,

```text
rank(u-1)<=12,               det(u)=1,                (CNR2)
rank(v-1)<=22,               det(v)=1.                (CNR3)
```

Thus no determinant charge survives on the actual canonical neutral
packet.  The remaining energy question is exactly the scalar trace deficit

```text
E_structural
 =||u-1||_F^2+||v-1||_F^2
 =2(2d-Re Tr(u)-Re Tr(v)).                            (CNR4)
```

All nonidentity spectrum in `(CNR4)` lies in the span of at most `34`
word-translates of the two rank-two source/exit carriers.  The subsequent
explicit mixed-carrier calculation
`neutral-weil-mixed-carrier-energy-tends-to-355-over-64` sharpens both
residual ranks to four and proves that their total Frobenius square tends
to `355/64`.
Neither strict separation nor determinant data decides between those two
outcomes.

The rank and determinant bounds alone do not give that floor: conjugate
eigenpairs can have determinant one and angles tending to zero.  The
positive limit uses the actual signed projective-line mixed carrier, not
only the ranks and principal angle.
