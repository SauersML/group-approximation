---
rg: 2
id: toms-schubert-algebra-misses-a-rank-via-constant-ranks
kind: route
title: If every continuous rank in Toms's algebra is constant, a non-constant continuous affine function is not a rank
target: toms-schubert-algebra-misses-a-rank
requires: [toms-schubert-algebra-continuous-ranks-are-constant, toms-doubling-ah-trace-simplex-is-poulsen]
---

`B` is unital, separable and nuclear, and `T(B)` is the Poulsen simplex by the
second prerequisite. In particular it has at least two points, so some
`b in B_sa` separates two traces. Put `f(tau) = tau(b) + ||b|| + 1`. This is a
strictly positive continuous affine function on `T(B)`, and it is not constant.

Suppose `f = d(a)` for some `a in (B tensor K)_+`. Then `d(a)` is finite and
continuous. By the first prerequisite it is constant, which is a contradiction.
So `f` is not a rank. Square.
