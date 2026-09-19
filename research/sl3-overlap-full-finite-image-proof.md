---
rg: 2
id: sl3-overlap-full-finite-image-proof
kind: route
title: Put Gamma(p squared) in the overlap and reduce at the coprime ambient level
target: sl3-overlap-full-in-fd-ambient-images
requires:
  - sl3-prime-permutation-codensity
---

The largest difference between two diagonal valuations of
`h=diag(p,1,p^(-1))` is two.  Hence conjugating a matrix congruent to the
identity modulo `p^2` by `h^(-1)` creates no denominator, and

```text
Gamma(p^2)<=C_+.                                       (OFIP1)
```

Finite-dimensional unitary superrigidity gives `sigma(A)` finite.  The
same CSP calculation used in `sl3-prime-permutation-codensity` puts a
principal congruence subgroup of some level `N`, with `(N,p)=1`, in the
kernel, so the image is a quotient of `SL_3(Z/N)`.

Reduction of `Gamma(p^2)` onto `SL_3(Z/N)` is surjective.  Indeed `p^2` is
a unit modulo `N`, so the matrices `x_ij(p^2 a)` realize every elementary
matrix modulo `N`, and elementary matrices generate `SL_3(Z/N)`.  Therefore

```text
sigma(Gamma(p^2))=sigma(C)=sigma(A).                    (OFIP2)
```

Together with `(OFIP1)`, this proves `(OFI1)`.  Taking commutants proves
`(OFI2)`.
