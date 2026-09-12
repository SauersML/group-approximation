---
rg: 2
id: stw83-circle-unitary-order-zero-gap-proof
kind: route
title: Use winding number against the finite order-zero star
target: stw83-circle-unitary-order-zero-plus-constants-gap
requires: []
---

An order-zero map from a finite-dimensional algebra to an abelian algebra
vanishes on every noncommutative matrix summand.  On the one-dimensional
summands it has the form

```text
eta(b)=sum_(j=1)^m lambda_j h_j,                         (4)
```

where `|lambda_j|<=1` and the `h_j` are pairwise orthogonal positive
contractions in `C(T)`.  Thus the image of

```text
g=c+eta(b):T->C
```

is contained in the finite star

```text
K=c+union_j [0,lambda_j].                               (5)
```

Suppose `norm(z-g)<1`.  The straight-line homotopy from `z` to `g`
avoids zero, because every point on it stays at distance strictly below
`1=|z|` from `z`.  Hence `g` has winding number one and in particular
never vanishes.

But `g(T)` is connected and lies in `K\{0}`, so it is contained in one
connected component of `K\{0}`.  The finite star `K` is a tree; every
component after removing one point is contractible in `C\{0}`.  Therefore
`g` is null-homotopic in `C\{0}` and has winding number zero, a
contradiction.  This proves `norm(z-c-eta(b))>=1`.  The zero map and zero
constant attain equality, so the infimum is exactly one.

For the plateau consequence identify `eDe` with `C(T)` and write

```text
e eta^(1)(b_1) e=c e.
```

Compression by `e` is contractive and fixes `eta^(0)(b_0)`.  Therefore

```text
norm(z e-eta^(0)(b_0)-eta^(1)(b_1))
 >= norm(z e-eta^(0)(b_0)-c e)
 >= 1.
```

No commutation between `e` and the second range was used; arbitrary
off-diagonal plateau transport remains allowed.
