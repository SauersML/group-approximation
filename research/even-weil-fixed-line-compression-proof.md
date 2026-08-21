---
rg: 2
id: even-weil-fixed-line-compression-proof
kind: route
title: Polar-round the compressed Weil involution and count one-dimensional excursions
target: even-weil-fixed-line-compression
requires:
  - iwahori-mod-p-quotient-is-psl2
  - bs14-unitary-representations-are-periodic-cycle-packets
---

In the Schrödinger model, the even Weil space has basis indexed by
`F_p/{+-1}`.  The zero basis vector spans the `R,S`-invariant fixed line and
the nonzero vectors span `H_0`.  For `A=PXP`, exact involutivity of `X` gives

```text
P-A^2=P X Q X P >=0
```

of rank at most one.  For every eigenvalue `a in [-1,1]`,
`(sgn(a)-a)^2 <= 1-a^2`; summing the eigenvalues proves the normalized bound
`||sgn(A)-A||_2 <= (dim H_0)^(-1/2)`.

Every compressed presentation word differs from the compression of the
exact full-space word by a bounded sum of terms containing `PXQ` or `QXP`.
Each such term has rank at most one and operator norm at most one, hence
normalized HS norm at most `(dim H_0)^(-1/2)`.  There are only boundedly many
terms because the four presentation words have fixed length.  Replacing
`A` by `sgn(A)` costs the same scale by word Lipschitzness.  This proves the
uniform `O(p^(-1/2))` estimate.

The exact nonextension follows from the mod-`p` quotient theorem and the
minimal character degree of `PSL_2(F_p)`; restoring `QH` gives the original
exact Weil model.
