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

For the ambient-central strengthening, let `X` be the finite orbit of `q`
under conjugation by `Gamma`; it is finite because the action on `C[K]`
factors through the finite group `Aut(K)`.  Choose one fixed representative
`h_x in Gamma` for every `x in X`, so `q_x=h_x q h_x^(-1)`.  Conjugating
`(FPP1)` by `h_x` gives, up to one fixed presentation-defect error,

```text
||(h_x g h_x^(-1)-I)Q_x||_2
 <= r epsilon+O(defect+exactification),                (FPP6)
```

where `g=w^(2r)`.  Centrality of `wK` in `Gamma/K` gives

```text
h_x g h_x^(-1)=k_x g,                  k_x in K.       (FPP7)
```

The word `g` centralizes `K`, and `k_x^e=1` for `e=exp(K)`.  Telescope
`(FPP6)` through the fixed power `e`; then `(k_xg)^e=g^e`, and hence

```text
||(g^e-I)Q_x||_2
 <= e r epsilon+O(defect+exactification).              (FPP8)
```

Now put

```text
z_Gamma=sum_(x in X) q_x.                              (FPP9)
```

This is positive, nonzero, and invariant under conjugation by all of
`Gamma`, so `z_Gamma in Z(C[Gamma])`.  Its support projection `p_Gamma` and
its inverse on that support are polynomials in `z_Gamma`, hence also lie in
`Z(C[Gamma])` and have finite support.  Sum `(FPP8)` over `X` and multiply
by that fixed inverse exactly as in `(FPP3)--(FPP5)`.  This proves `(FPR9)`.
The word `g^e=w^(2re)` still has infinite order.
