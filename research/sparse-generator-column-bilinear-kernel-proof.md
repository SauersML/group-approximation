---
rg: 2
id: sparse-generator-column-bilinear-kernel-proof
kind: route
title: Twist the Weyl form by an undetected bilinear matrix
target: sparse-generator-column-sampling-has-bilinear-kernel
requires:
  - generator-column-pauli-test-globalizes-but-does-not-pin-sites
---

The restriction map

```text
T_E:M_n(F_2)->F_2^E,
T_E(M)_(i,j)=a_i^T M b_j
```

has a nonzero kernel because its domain has dimension `n^2` and its codomain
has dimension `|E|<n^2`.  Choose `0!=M in ker(T_E)` and put `B=I+M`.
Factor `B=P^T Q` through `F_2^r`, where `r=rank(B)`.  On
`ell^2(F_2^r)` let

```text
X(a) delta_x=delta_(x+Pa),
Z(b) delta_x=(-1)^((Qb).x) delta_x.
```

These are exact representations of the two additive copies of `H` and

```text
X(a)Z(b)=(-1)^(a^T B b)Z(b)X(a).
```

Equation `(SGB1)` gives `(SGB3)`, and the usual normal form of a bilinear form
shows that `2^r` is the minimum scalar-Weyl carrier dimension.

For `(SGB4)`, the spectral-gap assumptions say, for every nonzero `v`,

```text
Pr_i[a_i.v=1]>=1/(2c),     Pr_j[v.b_j=1]>=1/(2c').       (SGB7)
```

Choose a nonzero row functional of `M`.  The second inequality implies
`Pr_j[M b_j!=0]>=1/(2c')`.  Conditional on `M b_j!=0`, the first inequality
gives

```text
Pr_i[a_i^T M b_j=1]>=1/(2c).
```

Hence a full random pair has the wrong ideal sign with probability at least
`1/(4cc')`.  On such a pair the two target unitaries differ by sign, so their
normalized squared Hilbert--Schmidt distance is four.  This proves `(SGB4)`.

Finally, minimizing the factor rank over all matrices in the affine fiber
`T_E^(-1)(T_E(I))` gives `(SGB6)` and the exact-strategy interpretation.
