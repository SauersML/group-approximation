---
rg: 2
id: stw84-scalar-fourier-row-two-colour
kind: claim
title: Scalar weighted Fourier rows admit two-colour mixed factorizations
distinct_from:
  stw84-bounded-overlap-fourier-gap: that theorem obstructs every fixed overlap depth on the Fourier diagonal; the present theorem realizes the surviving unbounded-mixing escape and gives a two-colour factorization of the full scalar row through the circle.
artifacts:
  - research/artifacts/stw84-scalar-fourier-row-two-colour-audit-2026-08-30.md
---

Let `A` be a unital C-star algebra, let `U in A` be unitary, and let
`h in A` be a positive contraction.  For `n>=1`, put

```text
Theta_(h,n)([c_ij])
 =n^(-1)sum_(i,j=0)^(n-1)
   c_ij h^(1/2)U^(i-j)h^(1/2).                        (SMF1)
```

For every finite `E subset M_n` and `epsilon>0`, there is `delta>0` such
that

```text
||[h,U]||<delta                                        (SMF2)
```

implies that `Theta_(h,n)` has, on `E`, an `epsilon`-accurate
finite-dimensional c.p. approximation with two c.p.c. order-zero return
colours.  Equivalently, asymptotically central weighted scalar Fourier rows
have nuclear dimension at most one locally, uniformly in the ambient
C-star algebra.

The diagonal mixing is even exact and one-coloured.  The restriction

```text
Lambda_(h,n)(z_0,...,z_(n-1))
 =n^(-1)(sum_i z_i)h                                  (SMF3)
```

factors as

```text
C^n --average--> C --(lambda |-> lambda h)--> A,       (SMF4)
```

whose return map is c.p.c. order zero.  Thus the growing-overlap escape
identified by `stw84-bounded-overlap-fourier-gap`
is genuinely attained: every coordinate image equals `h/n`, and the
overlap parameter grows like `n`.

For the augmentation carriers in
`stw84-augmentation-ideal-has-finite-dimensional-folner-carriers`,

```text
||[h,U]||=||h-alpha(h)||<=1/N.
```

Hence their scalar Fourier rows satisfy the theorem by taking `N` large.
The unresolved cyclic augmentation-ideal problem is therefore not caused
by the Fourier variable or the carrier weights separately.  It is exactly
the coefficient-valued covariance seam: for `M_n(D)` the corresponding
symbol takes values in `C(T) tensor D`, but evaluation by
`f tensor d |-> f(U)d` is not a star-homomorphism unless `U` commutes with
`D`.  The two circle colours proved here cannot simply be tensored with a
finite coefficient stage without paying for that covariance.
