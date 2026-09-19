---
rg: 2
id: steinberg-shear-fixed-labels-dimension-proof
kind: route
title: Count fixed dual labels of a coefficient multiplication shear
target: steinberg-shear-fixed-labels-recover-ideal-dimension
requires:
  - steinberg-root-shear-plancherel-covariance
---

Write an additive character of `H=A direct_sum A` as

```text
chi_(phi,psi)(a,c)=zeta^(phi(a)+psi(c)),
```

where `zeta` is a primitive `p`-th root and `phi,psi` are `F_p`-linear
functionals.  Since

```text
alpha_r^(-1)(a,c)=(a,c-ar),
```

the dual action sends

```text
(phi,psi) |-> (phi-psi compose R_r,psi),
R_r(a)=ar.                                              (SFP1)
```

It fixes `(phi,psi)` if and only if `psi compose R_r=0`, equivalently if
`psi` annihilates `Ar=im(R_r)`.  There are `p^n` choices for `phi` and
`p^(n-s(r))` choices for such a `psi`, proving `(SFD3)`.

Under the canonical delta trace on the finite subgroup `H`, every Fourier
atom has trace `|H|^(-1)=p^(-2n)`.  Summing the fixed atoms gives trace
`p^(-s(r))`.  The exact dual permutation fixes each of these atoms, hence
their sum commutes with the shear implementer.  The fixed-window
exactification and covariance estimates in
`steinberg-root-shear-plancherel-covariance` give `(SFD4)` by a finite sum
of normalized-HS errors.

The subgroup `L_r` in `(SFD4a)` is the additive image `Ar` in the second
root coordinate.  The Fourier expansion of its Reynolds projection is the
sum of precisely those character atoms which are trivial on `L_r`, namely
the labels satisfying `psi(Ar)=0`.  This proves `(SFD4b)`.

Now suppose `e,f` are orthogonal idempotents.  Every element of `A(e+f)` is
a sum of one element of `Ae` and one of `Af`.  If `xe=yf`, right
multiplication by `e` gives

```text
xe=xe^2=yfe=0,
```

so the intersection is zero.  This proves `(SFD5)` and the dimension
identity in `(SFD6)`.  A functional annihilates `A(e+f)=Ae direct_sum Af`
if and only if it annihilates both summands.  Therefore the corresponding
fixed-label sets intersect exactly, proving `(SFD8)`; uniform Plancherel
counting then gives the multiplicative trace identity in `(SFD6)`.
