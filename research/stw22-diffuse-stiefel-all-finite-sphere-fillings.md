---
rg: 2
id: stw22-diffuse-stiefel-all-finite-sphere-fillings
kind: claim
title: Diffuse finite-factor Stiefel spaces have one modulus in every finite sphere degree
distinct_from:
  stw22-diffuse-stiefel-uniform-four-sphere-fillings: that theorem is the last explicitly expanded induction stage; the present theorem proves the recursion in every finite degree.
  stw22-full-fundamental-group-weighted-copy-all-sphere-fillings: that theorem fixes a factor with full fundamental group; the present theorem is factor-uniform and assumes no corner isomorphisms, but only asserts each finite degree.
  stw22-hyperfinite-stiefel-all-sphere-fillings: that theorem uses hyperfiniteness; the present theorem applies to every separable-predual II1 factor.
artifacts:
  - research/artifacts/stw22-diffuse-all-degree-induction-audit-2026-08-31.md
---

Let `(N,tau)` range over all II1 factors with separable predual and let
`q in N` be a projection. For every finite integer `d>=0`, every
continuous map `S^d->St_N(q)` contained in the ball of radius

```text
rho_St(epsilon)=min(epsilon,1)^2/1000000              (AD-1)
```

about one point extends over `B^(d+1)` inside the concentric
`epsilon`-ball.

Every `St_N(q)` is `d`-connected for every finite `d`; in particular it
is weakly contractible. For each finite `d`, the family over all `N,q` is
uniformly equi-`LC^d`. The top-sphere input radius (AD-1) is independent
of `d`, the factor, and the corner.