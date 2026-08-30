---
rg: 2
id: consecutive-dyadic-splitting-no-dimension-proof
kind: route
title: Count dyadic leaf ranks and pad a divisible bulk
target: consecutive-dyadic-splitting-does-not-report-dimension
requires: []
---

Equivalent finite-dimensional projections have equal integer rank.
Induction down an exact orthogonal equal-child tree therefore gives every
depth-`j` leaf rank `k/2^j`; depth `r` forces `2^r` to divide `k`.  Numbers
`2^a(2n+1)` show that the stopping depth does not report size.

For the approximate statement write `k=2^r q+s`, `0<=s<2^r`.  On a
`2^r q`-dimensional bulk use the exact coordinate binary tree and its sibling
partial isometries; extend every nonroot operator by zero on the
`s`-dimensional residual space.  Every relation error vanishes on the bulk
and is supported on the residual projection `R`, whose normalized norm is

```text
||R||_2=sqrt(s/k)<sqrt(2^r/k).
```

Telescoping any fixed finite list of bounded star words changes this only by
a constant depending on its total word length, because multiplication by
contractions does not increase Hilbert--Schmidt norm.  For odd `k`, two
orthogonal rank-`(k-1)/2` children with an exact partial isometry leave only a
rank-one coverage residual, giving the sharp error `k^(-1/2)`.
