---
rg: 2
id: endpoint-constant-root-finite-quotient-proof
kind: route
title: Reduce the p-supported deviations and retain the prime-field matrix image
target: endpoint-constant-root-enlargements-have-marked-finite-quotient
requires:
  - endpoint-b2-enlargement-has-native-s3-retract
---

Every deviation coefficient of `P,J_1,J_2` is left-supported by
`p=s_0t_0`, and

```text
p(s_00t_1)=s_00t_1.
```

Thus the four matrices `P-I,J_1-I,J_2-I,B_2-I` have all entries in the
right ideal `pR`.  They preserve `(pR)^20` and induce the identity on

```text
A^20=(R/pR)^20.                                      (1)
```

The additive quotient `A` is nonzero: if `q=1-p` belonged to `pR`, say
`q=pr`, then left multiplication by `p` would give both `pq=0` and
`pq=q`, forcing `q=0`.

Every constant elementary root preserves `(pR)^20` and induces on `(1)`
the same zero-one elementary matrix.  Hence the image of the finite family
is contained in the finite group `GL_20(F_2)`, acting on the coordinate
factor and trivially on the coefficient factor.  More explicitly, if
`H_C=<x_78(1),x_87(1),C><=GL_20(F_2)`, the quotient action factors as

```text
G_C -> H_C -> Aut(A^20).                              (2)
```

The second arrow is injective.  If a zero-one matrix acts identically on
`A^20`, apply it to a coordinate vector carrying any fixed nonzero element
of `A`; its columns must equal those of the identity matrix.

In particular the two opposite transvections `n,m` retain their standard
faithful `GL_2(F_2)=S_3` action on coordinates `7,8`.  This proves `(PCR1)`
and the marked finite-image assertion.

For `x_84(1)`, direct multiplication with
`E=q(E_77+E_88)` gives

```text
E(x_84(1)-I)=qE_84!=0,
```

so this root really destroys that particular reducing corner.  It remains
a constant zero-one matrix in `(2)`, however, and therefore does not
destroy the marked finite quotient.  If it is the only added constant root,
the coordinate submodule `Ae_7+Ae_8` of `(1)` is invariant: `x_84(1)` has
source coordinate `4`, while `n,m` preserve coordinates `7,8`.  Restriction
to this submodule kills `x_84(1)` and retains the standard `S_3`, proving the
stronger retraction assertion in that case.

The finite-image argument applies to any finite family `C`, including
`x_47(1)` and the product obtained from the literal external return after
`J_1` becomes the identity on `(1)`.  An outward root such as `x_47(1)`
destroys the particular invariant coordinate submodule, but cannot destroy
the finite image `(2)`.
