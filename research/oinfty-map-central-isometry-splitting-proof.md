---
rg: 2
id: oinfty-map-central-isometry-splitting-proof
kind: route
title: Lift two central isometries and diagonalize the finite-set splitting defect
target: oinfty-map-stability-is-central-isometry-splitting
requires: []
---

## Proof

In any unital C-star algebra `D`, the unit is properly infinite exactly when
there are `s_1,s_2 in D` with `s_r^*s_t=delta_(r,t)1`.  Such a pair yields a
unital copy of `O_infinity`: the isometries

```text
t_n=s_2^(n-1)s_1,                         n>=1,
```

have pairwise orthogonal ranges.  Conversely, the first two canonical
isometries of a unital copy of `O_infinity` make the unit properly infinite.
Apply this first with `D=B_infinity intersect phi(A)'` to identify `(3)` with
the existence of a unital copy of `O_infinity` in that algebra.  For a unital
map the annihilator quotient in the usual map-relative central sequence
algebra is absent, since annihilating `phi(1)=1` forces an element to be zero.

If `kappa_phi(F)=0` for every finite `F`, choose increasing finite sets with
dense union in the unit ball of `A` and exact orthogonal isometry pairs whose
commutators on the `n`th set are below `1/n`.  Their classes in `B_infinity`
are two orthogonal isometries commuting with `phi(A)`.  Thus `(2)=>(3)`.

Conversely, take two orthogonal isometries in the `B_infinity` relative
commutant.  Choose
bounded representatives `x_(r,n)` in `B`.  Their row

```text
X_n=[x_(1,n) x_(2,n)] in M_(1,2)(B)
```

satisfies `X_n^*X_n -> 1_(M_2(B))`.  On a tail replace it by

```text
Y_n=X_n(X_n^*X_n)^(-1/2).
```

The two entries of `Y_n` are exact orthogonal isometries, and the correction
tends to zero.  Hence they still asymptotically commute with `phi(A)`, proving
`kappa_phi(F)=0`.

For the standard definition using `B_omega`, a unital copy of `O_infinity`
again gives two orthogonal central isometries.  For each finite set and
tolerance, choose one coordinate from the ultrafilter-large set on which the
relations and commutators have that tolerance, and apply the same row-polar
correction.  This proves `kappa_phi(F)=0`; separability diagonalizes the
resulting finite-set choices into `B_infinity`.  Conversely the quotient map
from `B_infinity` to `B_omega` carries a unital copy of `O_infinity` to a
unital (hence injective) copy.  Thus the standard `B_omega` definition, (2),
and (3) are equivalent.
