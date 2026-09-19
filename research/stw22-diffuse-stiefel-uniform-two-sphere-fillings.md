---
rg: 2
id: stw22-diffuse-stiefel-uniform-two-sphere-fillings
kind: claim
title: Diffuse finite-factor Stiefel spaces have a factor-uniform small two-sphere filling modulus
distinct_from:
  stw22-diffuse-stiefel-uniform-loop-fillings: that theorem supplies the degree-one modulus used to select the spectral supercarrier; the present theorem bootstraps it to degree two.
  stw22-hyperfinite-stiefel-all-sphere-fillings: that theorem has every finite degree but assumes the hyperfinite factor; the present theorem is degree two in an arbitrary separable-predual II1 factor.
artifacts:
  - research/artifacts/stw22-diffuse-two-sphere-supercarrier-audit-2026-08-30.md
---

Let `(N,tau)` be a II1 factor with separable predual and let `q in N`
be a projection. If

```text
x:S^2 -> Nq,             sup_z ||x(z)||_2 <= delta,
```

is `2`-norm continuous, then for every `kappa>0` there is a
`2`-norm-continuous projection field `e_z<=q`, of constant trace, such
that

```text
tau(e_z) <= min(tau(q),2 delta^2/kappa^2),
||x(z)(q-e_z)|| <= kappa.                              (SC2)
```

If `2 delta^2/kappa^2<tau(q)`, the selected trace is exactly
`2 delta^2/kappa^2`; otherwise one may take `e_z=q`.

Consequently the quadratic modulus

```text
rho_St,2(epsilon)=min(epsilon,1)^2/1000000              (DS2)
```

works simultaneously in every such factor: every continuous map
`S^2->St_N(q)` contained in the `rho_St,2(epsilon)`-ball about one of
its points extends over `B^3` inside the concentric `epsilon`-ball.
The modulus is independent of `N` and `q`.

Every `St_N(q)={v in N:v^*v=q}` is also two-connected. No
hyperfiniteness, property Gamma, McDuff absorption, or complement slack is
assumed. This is a diffuse II1 theorem; no matrix-factor two-sphere lifting
statement is included.
