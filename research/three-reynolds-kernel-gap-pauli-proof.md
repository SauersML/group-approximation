---
rg: 2
id: three-reynolds-kernel-gap-pauli-proof
kind: route
title: Diagonalize the full three-leg diagram Laplacian on one Pauli plane
target: three-reynolds-plus-kernel-energy-has-vanishing-gap
requires:
  - relative-finite-group-gh-cannot-fix-two-generating-subgroups
---

The matrices `B,C` anticommute, square to the identity, and commute with
`F`.  Thus `D_t` is a Hermitian involution and `F` commutes with both `A`
and `D_t`.  Every nonidentity value in `(DRK2)` has trace zero: if `g=1`,
the last tensor factor has trace zero; if `g=0`, this is the two-qubit Pauli
trace computation.  This proves the exact regular-character assertion.
Every nonexact multiplication cell is repaired by commuting `A` past `D_t`
once, and

```text
[A,D_t]=2sin(2t)AC,
```

which proves `(DRK3)--(DRK4)`.

The normalized-HS orthonormal real plane `V=span_R{B,C}` is invariant under
every term in `(DRK5)`.  Put `c=cos(2t)` and `s=sin(2t)`.  In the ordered
basis `(B,C)`, the Reynolds projections are

```text
E_A|V = [[1,0],[0,0]],
E_(D_t)|V = [[c^2,cs],[cs,s^2]],
E_F|V = I.                                             (DRK7)
```

Hence the local-angle part has matrix

```text
sum_U(I-E_U)|V = [[s^2,-cs],[-cs,1+c^2]],              (DRK8)
```

whose eigenvalues are `1-c` and `1+c`.

Conjugation by `A` is reflection across the `B` axis, while conjugation by
`D_t` is reflection across the axis `cB+sC`.  Therefore conjugation by
`Y_12=AD_tAD_t` is rotation through `-8t` on `V`.  It follows exactly that

```text
(I-Ad(Y_12))^*(I-Ad(Y_12))|V =4sin^2(4t) I.             (DRK9)
```

The other two kernel terms vanish by `(DRK4)`.  Combining `(DRK8)` and
`(DRK9)` shows that the smaller eigenvalue of `L_t|V` is

```text
lambda_t=1-cos(2t)+4sin^2(4t).
```

For `t>0`, the common fixed space of `E_A|V` and `E_(D_t)|V` is zero, so
this positive eigenvector is orthogonal to `ker L_t`.  Thus the global
spectral gap is at most `lambda_t`, proving `(DRK6)`.  Common amplification
does not change any displayed normalized-HS calculation.
