---
rg: 2
id: stw22-weighted-purification-all-sphere-fillings
kind: claim
title: Hyperfinite weighted purification fibres have uniform sphere fillings in every finite degree
distinct_from:
  stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling: that is the degree-one case; the present theorem proves every finite degree.
  stw22-hyperfinite-stiefel-all-sphere-fillings: that concerns projection weights; the present theorem permits arbitrary positive weights with support accumulating at zero.
artifacts:
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
---

Let `R` be the hyperfinite `II_1` factor, let `e in R` be a projection,
and fix `s<tau(e)`.  For

```text
F(a)={w in eR:w^*w=a},
0<=a<=1,       tau(supp(a))<=s,
```

the family of all `F(a)`, viewed in the common complete operator-norm unit
ball of `L^2(R)`, is uniformly equi-`LC^k` for every finite `k`.
Explicitly, for every `k>=0` and `epsilon>0` there is one
`rho_k(epsilon)>0`, independent of `a`, such that every continuous
`S^k`-map into one `F(a)` whose image lies in a
`rho_k(epsilon)`-ball about a point of that fibre extends over `B^(k+1)`
inside the corresponding `epsilon`-ball.

Every individual `F(a)` is `k`-connected for every finite `k`.  Neither
assertion assumes continuity or a spectral gap for `supp(a)`.
