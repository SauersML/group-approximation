---
rg: 2
id: stw22-diffuse-weighted-copy-uniform-s2-fillings
kind: claim
title: Strictly slack weighted-copy fibres in diffuse II1 factors have a factor-uniform two-sphere filling modulus
distinct_from:
  stw22-fixed-factor-weighted-copy-uniform-s2-fillings: that theorem permits an arbitrary fixed II1 factor but its modulus depends on that factor; the present theorem gives one modulus simultaneously for every separable-predual II1 factor.
  stw22-all-finite-factor-weighted-copy-uniform-loop-fillings: that theorem is factor-uniform in degree one and includes matrices; the present theorem reaches degree two for diffuse II1 factors only.
  stw22-weighted-purification-all-sphere-fillings: that theorem is all-degree but hyperfinite; the present theorem requires no amenability and stops at degree two.
artifacts:
  - research/artifacts/stw22-dim3-diffuse-bundle-breakthrough-2026-08-30.md
---

Let `(N,tau)` range over all II1 factors with separable predual. For
`m>=1` and a positive contraction `a in N`, put

```text
F_(N,m)(a)={(v_1,...,v_m):
  v_j^*v_j=a and (v_iv_i^*)(v_jv_j^*)=0 for i!=j}.    (W2-1)
```

Give tuples the Hilbert-sum `2`-metric. There is one function
`rho_W,2:(0,infinity)->(0,infinity)`, independent of `N,m,a` and the
amount of slack, such that whenever

```text
m tau(supp(a))<1,                                      (W2-2)
```

every map `S^2->F_(N,m)(a)` contained in the
`rho_W,2(epsilon)`-ball about one of its points extends over `B^3`
inside the concentric `epsilon`-ball.

Every fibre in (W2-1) satisfying (W2-2) is two-connected. Together with
the factor-uniform path and loop theorems, these fibres form one
equi-`LC^2` family across all separable-predual diffuse factors, all copy
numbers, all positive weights, and every positive complement slack.

The theorem does not include matrix factors. Their stabilizers can carry a
fundamental-group obstruction to the diffuse unitary-lift method used here;
no claim is made about other matrix-specific filling methods.