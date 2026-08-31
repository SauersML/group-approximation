---
rg: 2
id: stw22-diffuse-stiefel-uniform-four-sphere-fillings
kind: claim
title: Diffuse finite-factor Stiefel spaces have a factor-uniform small four-sphere filling modulus
distinct_from:
  stw22-diffuse-stiefel-uniform-three-sphere-fillings: that theorem supplies the degree-three corner control used here; the present theorem bootstraps it by one dimension.
  stw22-full-fundamental-group-weighted-copy-all-sphere-fillings: that theorem is all-degree after fixing a full-fundamental-group factor; the present degree-four modulus is uniform over every separable-predual II1 factor.
artifacts:
  - research/artifacts/stw22-diffuse-four-sphere-supercarrier-audit-2026-08-31.md
---

Let `(N,tau)` be a II1 factor with separable predual and `q in N` a
projection. The universal modulus

```text
rho_St,4(epsilon)=min(epsilon,1)^2/1000000             (DS4)
```

has the following property: every continuous map `S^4->St_N(q)` contained
in the `rho_St,4(epsilon)`-ball about one point extends over `B^5` inside
the concentric `epsilon`-ball.

Every `St_N(q)={v:v^*v=q}` is four-connected. The modulus is independent
of `N` and `q`; no hyperfiniteness, full fundamental group, property
Gamma, McDuff absorption, or complement slack is assumed.

Equivalently, for every continuous `x:S^4->Nq` with
`sup||x||_2<=delta` and every `kappa>0`, there is a continuous
constant-trace supercarrier `e_z<=q` satisfying

```text
tau(e_z)<=min(tau(q),2delta^2/kappa^2),
||x(z)(q-e_z)||<=kappa.                               (SC4)
```