---
rg: 2
id: finite-quotient-carmichael-coloring-proof
kind: route
title: Color each vertex by the image of its conjugate in one finite quotient
target: finite-quotients-bound-carmichael-conjugacy-chromatic-number
requires: []
---

Color a vertex `v` by `phi(u_v)`, which lies in the finite conjugacy class
`phi(w)^Q`.  If adjacent vertices `v,z` had the same color `x`, then `(FQC1)`
would give

```text
x^3=1,             (x x)^2=x^4=1.
```

Since `gcd(3,4)=1`, this forces `x=1`, contradicting that `x` is conjugate to
the nonidentity element `phi(w)`.  The coloring is proper, proving `(FQC2)`.

For the last statement in the claim, let `L_n` be the maximum defining-
relator area of all cube and edge loops in a graph `Lambda_n`.  If a
subsequence with `chi(Lambda_n)->infinity` had bounded `L_n`,
`bounded-area-high-chromatic-conjugacy-collapse` would kill `w` in every
tracial matrix-ultraproduct representation.  A regular-character embedding
of a hyperlinear group separates every nonidentity `w`, so `L_n` must tend
to infinity.

