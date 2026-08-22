---
rg: 2
id: finite-packet-localized-return-centralizes-after-power-proof
kind: route
title: Telescope the return, average its finite conjugacy orbit, and invert the Reynolds element on its support
target: finite-packet-localized-return-centralizes-after-power
requires: []
---

Write `A=W^2`.  The elementary factorization

```text
(A^r-I)Q=sum_(j=0)^(r-1) A^j(A-I)Q
```

gives

```text
||(W^(2r)-I)Q||_2<=r epsilon.                          (FPP1)
```

In `C[K]` form the positive Reynolds element

```text
z=sum_(k in K) k q k^(-1).                             (FPP2)
```

It is nonzero and central in `C[K]`.  Let `p` be its support projection.
Because `C[K]` is finite dimensional, `p` and the inverse of `z` on its
support both belong to `C[K]`: there is a fixed `b in Z(C[K])` such that

```text
p=zb,                    ||b||<infinity.               (FPP3)
```

After exactification the evaluated matrices satisfy the same identities.
Put `G=W^(2r)` and `Z=sum_k U_k Q U_k^*`.  For each `k`,

```text
(G-I)U_k Q U_k^*
 =U_k(G-I)Q U_k^* + [G,U_k]Q U_k^*.                   (FPP4)
```

The first term has normalized Hilbert--Schmidt norm at most `r epsilon` by
`(FPP1)` and the second at most `gamma`.  Summing `(FPP4)` and multiplying
on the right by the fixed matrix `B=b(U)` yields

```text
||(G-I)P||_2
 <= |K| ||b|| (r epsilon+gamma),                       (FPP5)
```

which is `(FPR5)`.

The covariance error really is controlled by the presentation defect.  For
each of the finitely many `k in K`, the equality `[w^(2r),k]=1` has one fixed
van Kampen diagram over `<S|R>`.  Telescoping that diagram gives a fixed
multiple of the maximum relator defect; changing the finite packet during
exactification adds only a fixed Lipschitz multiple of its generator error.

Finally `g=w^(2r)` centralizes `K`.  Since `g` has infinite order and `K` is
finite, `<g> intersect K={1}`, proving `(FPR6)`.  Map `g` to a generator of
`Z/N` and retain `K` faithfully.  In the finite regular representation the
two terms `gp` and `p` occupy distinct `K` cosets.  Equivalently, expanding
the square and using the coefficient trace,

```text
tau_N(p g^(-1) p)=tau_N(p g p)=0,
tau_N((gp)^*(gp))=tau_N(p^2)=tau_N(p).
```

Thus the squared norm is `2 tau_N(p)=2 tau(p)`, proving `(FPR7)`.

