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

The Schrodinger Fourier formula makes this exact.  With
`Q=|delta_0><delta_0|`, put `v=PX delta_0`.  Then

```text
|<delta_0,X delta_0>|^2=1/p,
||v||^2=1-1/p,
P-A^2=|v><v|.
```

Hence `A^2` is the identity on `v^perp` and has eigenvalue `1/p` on
`C v`.  Since `A` is selfadjoint, its singular values are one off `C v`
and `p^(-1/2)` on `C v`.  Replacing that one singular value by one proves
the identity `(EWC3')`.  It also shows that both off-diagonal excursions
have unnormalized Frobenius norm squared `1-1/p`, so the deleted-line
boundary is genuinely rank one rather than a diffuse estimate artifact.

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

For strict separation, fix a `(T;FD)` Kazhdan pair for
`PSL_2(Z[1/2])`.  If exact same-dimensional `sigma_p` approached the
compressed tuple, then `sigma_p (+) 1` and the irreducible full Weil
representation `pi_p` would be closer than the Kazhdan constant for large
`p`.  The identity matrix is then an almost-invariant unit vector in
`pi_p tensor conjugate(sigma_p (+) 1)`.  Property `(T;FD)` produces a
nonzero invariant vector, equivalently a nonzero intertwiner.  Irreducibility
and equality of total dimensions force `sigma_p (+) 1 ~= pi_p`, contradicting
the invariant trivial line on the left.  The same argument gives a uniform
positive lower bound after subtracting the `O(p^(-1/2))` compression error.
