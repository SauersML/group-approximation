---
rg: 2
id: norm-corona-isometry-proof
kind: route
title: Polar correction of a bounded lift proves norm-corona isometries are unitary
target: norm-matrix-corona-has-no-proper-isometries
requires: []
---

## Direct proof

Let `v in C` with `v* v=1` and choose a bounded lift `(x_n)` in
`prod_n M_(d_n)`.  The relation `v* v=1` says

```text
||x_n* x_n - I|| -> 0,
```

so for all large `n` the positive matrix `x_n* x_n` is bounded below by
`1/2`, hence invertible.  Each `x_n` is **square**, so invertibility of
`x_n* x_n` makes `x_n` invertible.  Functional calculus gives the polar
unitary

```text
u_n = x_n (x_n* x_n)^(-1/2),
```

and `||x_n-u_n|| = ||x_n((x_n* x_n)^(-1/2)-I)|| -> 0` because
`(x_n* x_n)^(-1/2) -> I` in norm and `(x_n)` is bounded.  Therefore
`v=[u_n]` in the quotient and `v v* = [u_n u_n*] = 1`.

Squareness is the whole content: the same computation in
`prod_n B(H)/direct_sum_n B(H)` fails, because a lift of a proper isometry is
not invertible.  This is the exact-corona shadow of the finite-dimensional
rank identity `rank(x)=rank(x*)`.
