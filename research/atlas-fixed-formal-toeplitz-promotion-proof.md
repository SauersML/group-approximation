---
rg: 2
id: atlas-fixed-formal-toeplitz-promotion-proof
kind: route
title: Detect the first nonzero series coefficient by linear rank, then specialize
target: atlas-fixed-formal-toeplitz-microstates-promote
requires:
  - atlas-exact-matrix-zero-set-is-a-finite-quotient-test
---

The quotient map

```text
F2[[z]] -> F2[z]/(z^N)
```

followed by multiplication is a ring homomorphism.  It sends `B(z)` to
`T_N` and `B(z)^-1` to `T_N^-1`.  Hence evaluation of each Atlas Laurent
word at `T_N` is exactly multiplication by the corresponding formal matrix
residual `R(B(z))`, reduced modulo `z^N`.

Suppose a formal matrix `F(z)` is nonzero.  Choose one entry

```text
f(z)=z^k u(z),   u(0)!=0.
```

For `N>k`, multiplication by `f` on `F2[z]/(z^N)` has kernel dimension `k`
and rank `N-k`, since multiplication by `u` is invertible.  Restricting the
full block operator to the corresponding input coordinate and projecting to
the chosen output coordinate shows

```text
rank(mult_(F mod z^N)) >= N-k.                        (FTP3)
```

Thus a nonzero fixed formal residual has positive asymptotic normalized rank
(at least `1/b` before the harmless `k/N` term).  The hypothesis that every
residual has rank `o(N)` forces all of them to vanish formally, proving
`(FTP2)`.

Finally regard the entries of one unknown `b`-by-`b` matrix, together with
one variable for its inverse determinant, as coordinates of a finite affine
system over `F2`.  The point `B(z)` over the field `F2((z))` proves that its
coordinate algebra is nonzero.  A maximal ideal has residue field finite
over `F2` by Zariski's lemma, hence equal to `F_(2^f)` for some `f`.  The
resulting closed point is invertible and satisfies every augmented relation
exactly.  The established exact-zero theorem then supplies the finite binary
escape after restriction of scalars.

