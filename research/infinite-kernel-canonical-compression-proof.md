---
rg: 2
id: infinite-kernel-canonical-compression-proof
kind: route
title: A regular representation has no invariant vector for an infinite subgroup
target: infinite-kernel-canonical-compression-is-zero
requires: []
---

Assume that a projection `p` satisfies `(IKC1)`.  For every `n in N`,

```text
||(u_n-1)p||_2^2
 = tau(p (u_n^*-1)(u_n-1) p)
 = 2 tau(p)-2 Re tau(p u_n p)
 = 0.
```

Hence `u_n p=p` as a vector in `L^2(L(W))` for every `n in N`.

The left multiplication representation of `W` on `L^2(L(W))` is its left
regular representation on `ell^2(W)`.  On restriction to `N`, choose one
representative from each left coset of `N` in `W`; the corresponding coset
subspaces give an orthogonal decomposition into copies of `ell^2(N)`.
Thus the restricted representation is an amplification of `lambda_N`.

The regular representation of an infinite group has no nonzero invariant
vector: an invariant function on `N` is constant, and a nonzero constant
function is not square-summable.  Therefore the only `N`-invariant vector in
`ell^2(W)` is zero.  It follows that `p=0`, contradicting the assumption that
the projection was nonzero and proving the claim.
