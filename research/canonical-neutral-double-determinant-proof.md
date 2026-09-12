---
rg: 2
id: canonical-neutral-double-determinant-proof
kind: route
title: Round both cyclic carriers independently and conserve their conjugate determinants
target: neutral-weil-symmetric-retraction-is-double-neutral
requires:
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
  - two-cubic-residual-carriers-recover-the-deleted-source
  - even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two
  - exact-torsion-frame-has-rank-one-strict-counterpackets
---

For `p=1 mod 8`, both `U_1=T=S^2` and `U_2=RS=T^2R` fix the deleted line
`Cq`, and `(XU_i)^3=1` in the full even-Weil representation.  The
positive-corner carrier calculation therefore applies to both compressed
unitaries `A_old=X_0U_1` and `B_old=X_0U_2`: each cubic residual has rank
exactly two.  Its two exceptional eigenvalues are a conjugate pair
`lambda,lambda^(-1)`, while all other eigenvalues are already cube roots.
Nearest cube-root rounding replaces the exceptional pair by a conjugate
pair of cube roots.  Consequently

```text
rank(A-A_old)<=2,     det(A)=det(A_old),
rank(B-B_old)<=2,     det(B)=det(B_old).               (CND1)
```

The symmetric definitions `(CNR1)` give

```text
rank(T_1-T)<=2,
rank(R_1-R)<=2 rank(T_1-T)+rank(B-B_old)<=6.          (CND2)
```

The old inversion and BS rows are exact.  Telescoping the two `R`
occurrences in inversion proves `rank(u-1)<=12`.  In the BS word, the two
`R` occurrences cost twelve, the single `T` costs two, and the four copies
in `T^4` cost eight, proving `rank(v-1)<=22`.

For determinants, every exact torsion frame satisfies

```text
det(v)=det(T_1)^(-3)=det(X),
det(u)=(det(A)det(B))^2.                              (CND3)
```

By `(CND1)` and the definitions before rounding,

```text
det(A)det(B)
 =det(XT)det(XT^2R)=det(T)^3det(R).                   (CND4)
```

Exact old BS covariance implies `det(T)^3=1`, and exact old inversion
implies `det(R)^2=1`.  Squaring `(CND4)` proves `det(u)=1`.  On the even
Fourier space, the negative multiplicity of `X` is `(p-1)/4`; it is even
for `p=1 mod 8`.  Polar compression preserves this determinant and the
retraction leaves `X` fixed, proving `det(v)=1`.

Finally `(CNR4)` is the standard Frobenius trace identity for unitaries.
The range of each residual is contained in the sum of the ranges appearing
in the rank telescoping above, giving a carrier of dimension at most
`12+22=34`.  This proves the finite-rank reduction and the determinant
firewall.
