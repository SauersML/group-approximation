---
rg: 2
id: osin-group-times-z-has-bvc-proof
kind: route
title: Every element of O × Z is conjugate to a power of (g,1), (g,0) or (1,1)
target: osin-group-times-z-has-bvc
requires:
  - osin-torsion-free-two-conjugacy-class-groups-exist
---

Let `O` be finitely generated, torsion-free, with two conjugacy classes. Fix `g != 1`.

1. **Every element of O is a k-th power.** For `k != 0`, `g^k != 1` because `O` is
   torsion-free, so `g^k` is conjugate to `g`. Write `g = w g^k w^{-1} = (w g w^{-1})^k`.
   So `g` has a `k`-th root `y_k = w g w^{-1}`, and `y_k` is conjugate to `g`.
2. **Classification of elements of `G = O × Z`.**
   - `(1, m) = (1,1)^m`.
   - For `x != 1`: `x` is conjugate to `g`, so `(x, 0)` is conjugate to `(g, 0) = (g,0)^1`.
   - For `x != 1` and `m != 0`: `x` is conjugate to `y_m` (both are nontrivial), so `(x, m)`
     is conjugate to `(y_m, m) = (y_m, 1)^m`, which is conjugate to `(g, 1)^m` since `y_m` is
     conjugate to `g`.
3. **BVC.** `G` is torsion-free, so by von Puttkamer–Wu arXiv:1607.03790, Corollary 1.5, it
   has BVC exactly when finitely many elements have every element conjugate to a power of one
   of them. Step 2 gives the three elements `(g,1)`, `(g,0)`, `(1,1)`. Directly: every
   virtually cyclic subgroup of a torsion-free group is cyclic, and step 2 conjugates each
   cyclic subgroup into one of the three cyclic witnesses.
4. **Not virtually cyclic.** `O` is nontrivial and not `Z` (`Z` has infinitely many conjugacy
   classes), so the torsion-free group `O` is not virtually cyclic. Hence neither is
   `G >= O × {0}`. Projection onto the second factor maps `G` onto `Z`.
