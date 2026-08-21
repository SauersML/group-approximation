---
rg: 2
id: regular-simplex-proves-raw-gram-local-gap-vanishes
kind: route
title: Use the regular simplex whose every bounded Gram window becomes orthonormal
target: raw-gram-rank-overflow-has-no-constant-local-gap
requires: []
---

In `C^(r+1)` let `e_i` be the standard basis, let

```text
m=(1/(r+1)) sum_i e_i,
v_i=sqrt((r+1)/r) (e_i-m).
```

The vectors lie in the codimension-one hyperplane `m^perp`, which is
isomorphic to `C^r`, and their sum is zero.  Direct calculation gives

```text
<e_i-m,e_i-m>=r/(r+1),
<e_i-m,e_j-m>=-1/(r+1)       for i!=j.
```

After normalization this is `(RGO1)`.  The full Gram matrix is singular
because `sum_i v_i=0`, and the vectors span `m^perp`, so its rank is exactly
`r`.

For a subset of size `ell<=k`, the restricted Gram matrix is

```text
(1+1/r) I_ell - (1/r) J_ell.
```

Its difference from `I_ell` has eigenvalues `-(ell-1)/r` once and `1/r`
with multiplicity `ell-1`; hence its operator norm is at most `(k-1)/r`.
Uniform continuity on the compact space of bounded `k` by `k` Gram matrices
now proves convergence for every fixed bounded continuous local predicate.

