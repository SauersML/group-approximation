---
rg: 2
id: jacobson-matrix-coefficient-shadows-pay-head-by-index-proof
kind: route
title: Split the head image into the TS relator and its AB mirror, and conjugate one to the other by equal rank
target: jacobson-matrix-coefficient-shadows-pay-head-by-index
requires: []
---

Notation as in the target. Everything below is linear algebra over a field `F` of characteristic `2`, plus
conjugation invariance and subadditivity of the metric.

## Step 1. Exact image of the head

For any ring `R`, distinct `i, j, k`, and `a, b in R`, the Steinberg commutator identity holds in `GL_n(R)`:
`[X_ij(a), X_jk(b)] = X_ik(ab)`, with `[g,h] = g h g^(-1) h^(-1)`. Take `R = M_N(F)`. Then

```text
rho(r) = [X_12(B), X_23(A)] X_13(1)^(-1) = X_13(BA - 1) = X_13(e_1),             e_1 = 1 - BA,
rho(z) = [X_12(B), X_23(A)] [X_12(A), X_23(B)] = X_13(BA + AB).
```

In characteristic `2`, `BA + AB = (1 - BA) + (1 - AB) = e_1 + e_2` with `e_2 = 1 - AB`. Since
`X_13(c) X_13(c') = X_13(c + c')`,

```text
rho(z) = X_13(e_1) X_13(e_2).                                                       (1)
```

## Step 2. Finite-dimensional index zero

`rk(1 - AB) = rk(1 - BA)` for all `A, B in M_N(F)`. Proof: if `ABv = v`, then `BA(Bv) = Bv`, and `Bv = 0`
would give `v = ABv = 0`. So `B` maps `ker(1 - AB)` injectively into `ker(1 - BA)`. Symmetrically, `A` maps
`ker(1 - BA)` injectively into `ker(1 - AB)`. So the kernels have equal dimension, and the ranks are equal
because both matrices are `N x N`.

## Step 3. The AB half is conjugate to the relator

Two `N x N` matrices of equal rank are equivalent, so `e_2 = u e_1 w^(-1)` for some `u, w in GL_N(F)`. Let
`D = diag(u, 1, w, 1, ..., 1) in GL_n(M_N(F))`. Then

```text
D X_13(e_1) D^(-1) = 1 + E_13 (x) (u e_1 w^(-1)) = X_13(e_2).                      (2)
```

## Step 4. The bound

Let `d(g) = ||sigma(g) - 1||_2`, or the normalized Hamming distance of `sigma(g)` from the identity. Then `d`
is conjugation invariant, since `sigma(D)` is unitary or a permutation. It is also subadditive:
`d(gh) <= d(g) + d(h)`. By (1) and (2),

```text
d(rho(z)) <= d(X_13(e_1)) + d(X_13(e_2)) = 2 d(X_13(e_1)) = 2 d(rho(r)).
```

This is (MCS). The consequence for sequences is immediate, since `r = 1` in `EL_n(J)`, so an approximation
has `d(rho_k(r)) -> 0`. QED.

## Remark (dependence)

Only the letters `x_12(S), x_12(T), x_23(S), x_23(T), x_13(1)` are used. No other relation of `EL_n(J)` is
used, and no Property `(T)` input. The bound therefore holds verbatim for models defined only on the
subgroup these letters generate.
