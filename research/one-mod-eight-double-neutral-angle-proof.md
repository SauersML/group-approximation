---
rg: 2
id: one-mod-eight-double-neutral-angle-proof
kind: route
title: Bound the normalization ranks and exhaust the finite determinant charges
target: one-mod-eight-torsion-charge-reduces-to-a-double-neutral-angle
requires:
  - iwahori-two-triangle-torsion-normal-form
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
  - even-weil-fixed-line-compression
---

Use the notation of the torsion-normalization proof.  Before normalization,
the first compressed cubic residual has rank at most two and the second has
rank at most six.  For the second bound, insert `P+q` in the two internal
slots of the exact full-space cubic (three rank-one compression terms), then
telescopically replace `PXP` by its polar sign (three more rank-one terms);
this rank calculation is independent of the quadratic character of two.
Hence nearest cube-root rounding gives

```text
rank(A-A_old)<=2,             rank(T_1-T)<=2.
```

Writing `B_old=XT^2R` and `B_1=XT_1^2R`, fixed-word rank telescoping gives

```text
rank(B_1-B_old)<=4,
rank(B_1^3-1)<=6+3(4)=18,
rank(B-B_1)<=18,
rank(R_1-R)<=18.                                    (ONA1)
```

The original inversion and BS rows are exact.  Changing the two `R`
occurrences in inversion gives

```text
rank(u-1)<=2(18)=36.                                 (ONA2)
```

Changing the two `R` occurrences, the one `T` occurrence, and the four
copies in `T^4` gives

```text
rank(v-1)<=18+2+18+4(2)=46.                          (ONA3)
```

For every exact torsion frame,

```text
det(v)=det(T)^(-3)=det(X),
det(u)=(det(X)det(R))^2=(det(A)det(B))^2 in mu_3.    (ONA4)
```

The last equality follows directly from
`R=A^2XA^2B`, `X^2=1`, and `A^3=B^3=1`.  In the even Fourier model,
`Tr(X)=1` on dimension `(p+1)/2`, so the negative multiplicity is
`(p-1)/4`.  It is even for `p=1 mod 8`; polar compression preserves the
determinant and normalization leaves `X` fixed.  Therefore `det(v)=1`.

If `det(u)` is a nontrivial cube root, then

```text
3=|det(u)-1|^2<=rank(u-1)||u-1||_F^2<=36||u-1||_F^2,
```

which proves `(ONT3)`.  If it is trivial, both determinants are one.  The
explicit matrices `(ONT5)` prove that no positive lower bound follows from
rank, determinant, nonidentity, or conjugate-pair symmetry alone.  Finally,
nearest cube-root rounding replaces the two exceptional first-cubic
eigenvalues by conjugate cube roots, so their product is one: the uniform
pre-normalization energy from
`deleted-fixed-line-first-cubic-has-explicit-positive-spectrum` carries no
scalar determinant charge across that step.  This isolates the asserted
post-normalization eigenangle lemma.
