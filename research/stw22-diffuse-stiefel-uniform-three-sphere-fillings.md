---
rg: 2
id: stw22-diffuse-stiefel-uniform-three-sphere-fillings
kind: claim
title: Diffuse finite-factor Stiefel spaces have a factor-uniform small three-sphere filling modulus
distinct_from:
  stw22-diffuse-stiefel-uniform-two-sphere-fillings: that theorem supplies the degree-two stabilizer and Grassmannian control used here; the present theorem bootstraps it by one dimension.
  stw22-full-fundamental-group-weighted-copy-all-sphere-fillings: that theorem obtains all degrees after fixing a factor with full fundamental group; the present theorem is degree three, factor-uniform, and assumes no corner isomorphisms.
artifacts:
  - research/artifacts/stw22-diffuse-three-sphere-supercarrier-audit-2026-08-31.md
---

Let `(N,tau)` be a II1 factor with separable predual and let `q in N` be
a projection. If

```text
x:S^3->Nq,             sup_z ||x(z)||_2<=delta,
```

is `2`-norm continuous, then for every `kappa>0` there is a continuous
projection field `e_z<=q`, of constant trace, such that

```text
tau(e_z)<=min(tau(q),2delta^2/kappa^2),
||x(z)(q-e_z)||<=kappa.                               (SC3)
```

Consequently

```text
rho_St,3(epsilon)=min(epsilon,1)^2/1000000             (DS3)
```

works simultaneously in every such factor: every continuous map
`S^3->St_N(q)` contained in the `rho_St,3(epsilon)`-ball about one of
its points extends over `B^4` inside the concentric `epsilon`-ball.

Every `St_N(q)={v in N:v^*v=q}` is three-connected. The modulus is
independent of `N` and `q`. No hyperfiniteness, full fundamental group,
property Gamma, McDuff absorption, or complement slack is assumed.