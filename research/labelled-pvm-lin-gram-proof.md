---
rg: 2
id: labelled-pvm-lin-gram-proof
kind: route
title: Sum the orthogonal branch blocks and polar-cancel on each spectral layer
target: labelled-pvm-branch-gram-gives-lin-corner
requires: []
artifacts:
  - research/artifacts/labelled-pvm-lin-gram-audit-2026-08-23.md
---

Put `B_i=F_iT_iE_i`.  For `i!=j`, both `B_i^*B_j` and `B_iB_j^*` vanish by
orthogonality of the `F` and `E` families.  Summing the remaining diagonal
terms proves `(LBG2)--(LBG3)`.

Equation `F_iG=GE_i` implies

```text
E_iG^*G=G^*F_iG=G^*GE_i.
```

Hence `E_i` commutes with `|G|` and all its spectral projections.  In the
polar decomposition, `F_iU|G|=UE_i|G|`; on a positive spectral layer one
may cancel `|G|`, proving `(LBG4)`.

For the binary specialization decompose

```text
T=sum_(a,b)F_aTE_b.
```

These blocks are Hilbert--Schmidt orthogonal.  The diagonal blocks sum to
`G`, while on the `(a,b)` block the `j`th covariance row is multiplication
by `a_j-b_j`.  Therefore

```text
sum_j||D_j||_2^2
 =4 sum_(a,b) Hamming(a,b)||F_aTE_b||_2^2.
```

Off the diagonal the Hamming distance lies between one and two, proving
`(LBG5)`.  Pythagoras and `||T||_2^2=tau(Q)` give the mass bound in
`(LBG6)`.

Finally, direct expansion with `D_j=A_jT-TZ_j` gives

```text
D_j^*T-T^*D_j=QZ_j-Z_jQ=[Q,Z_j].
```

The triangle inequality and `||T||<=1` prove the last estimate.  The cyclic
label shift in the artifact has every diagonal block zero, proving that the
positive-mass clause cannot be deleted.

For the one-bit specialization, write `F_e=(1+eA_X)/2` and
`E_e=(1+eZ_X)/2`.  The four blocks `F_eTE_f` are Hilbert--Schmidt
orthogonal.  Their two diagonal blocks sum to `G_X`, whereas

```text
D_X=2F_+TE_- - 2F_-TE_+.
```

This proves `(LBG8)`, and Pythagoras with `||T||_2^2=tau(Q)` proves
`(LBG9)`.  The triangle inequality gives

```text
||A_YG_X-G_XZ_Y||_2
 <=2||G_X-T||_2+||A_YT-TZ_Y||_2
 =||D_X||_2+||D_Y||_2.
```

Finally, if `A_X` and `A_Y` commute and
`R_Y=A_YG_X-G_XZ_Y`, use `A_XG_X=G_XZ_X` to expand

```text
A_XR_Y-R_YZ_X=-G_X[Z_X,Z_Y].
```

This proves `(LBG10)--(LBG11)` and shows exactly why only one source
endpoint must be made into the label PVM before the Lin step.
