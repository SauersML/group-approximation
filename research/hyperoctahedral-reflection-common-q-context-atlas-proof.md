---
rg: 2
id: hyperoctahedral-reflection-common-q-context-atlas-proof
kind: route
title: Reserve one signed coordinate and repeat the rational balanced atlas on its complement
target: hyperoctahedral-reflection-common-q-context-atlas
requires:
  - tracial-bcs-has-rational-balanced-hyperoctahedral-atlas
---

The full diagonal sign subgroup and the permutation subgroup generate the
tautological signed-permutation representation irreducibly: a nonzero
invariant subspace is invariant under all coordinate sign cuts, hence
contains a coordinate line, and transitivity of `S_N` then supplies every
coordinate line.  Thus its primitive central projection `p` has corner
`p C[K_N] p isomorphic to M_N(C)`.

In this block `s` is `diag(-1,1,...,1)`.  Hence `e` and `q` have ranks one
and `N-1=tD`, respectively.  The canonical trace normalized on a primitive
Fourier block is normalized matrix trace, proving `(HRC4)`.

Label the nonzero coordinates, separately for each context `c`, by

```text
{(a,j):a in R_c, 1<=j<=t n_(c,a)}.                         (HRC6)
```

For `x in U_c`, define `d_(c,x)` to have sign `a_x` on `(a,j)` and sign
`+1` on coordinate zero.  These elements lie in the diagonal `(C_2)^N`, so
they are commuting involutions and commute with `s`.  Their joint spectral
atom on `q` belonging to `a` is the sum of precisely the coordinate
projections labelled `(a,j)`.  It consequently has rank `t n_(c,a)`, and no
forbidden assignment occurs.

For a shared variable `x`, the rational balance equations say that the
numbers of `+1` and `-1` coordinates for `d_(c,x)` and `d_(d,x)` agree.
Choose bijections between the corresponding sign fibers and fix coordinate
zero.  Their union is a permutation `pi_(c,d,x) in S_(N-1)` and gives
`(HRC5)` as an identity already in the finite group.  Repetition by `t`
does not affect balance and makes `1/N` arbitrarily small.
