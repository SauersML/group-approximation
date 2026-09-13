---
rg: 2
id: toms-schubert-algebra-misses-a-rank-via-leaf-average
kind: route
title: If no leaf-average function is a rank in B, the strictly positive leaf average tau((1+h)/2) is an unrealized rank
target: toms-schubert-algebra-misses-a-rank
requires: [toms-simple-algebra-realizes-no-leaf-average-rank]
---

Let `h in C(X_1)` be non-constant with `0 <= h <= 1`. Toms's `X_1 = Gr(d,2d)` has
infinitely many points, so such `h` exist. Put `h' = (1 + h)/2`. Then `h'` is
non-constant and `1/2 <= h' <= 1`, and `h' in C(X_1) ⊂ B_1` pushes forward to `B`.

Put `f(tau) = tau(h')`. It is continuous and affine on `T(B)`, and `f >= 1/2 > 0`, so
`f` is a strictly positive continuous affine function. By the prerequisite
applied to `h'`, no `a in (B tensor K)_+` has `d(a) = f`. So `f` is not a rank,
which is the target. Square.
