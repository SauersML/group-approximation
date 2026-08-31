---
rg: 2
id: stw22-half-slack-all-factor-weighted-copy-finite-degree-fillings
kind: claim
title: Eventually replicated half-slack weighted fibres have factor-uniform fillings in every fixed finite degree
distinct_from:
  stw22-matrix-weighted-copy-uniform-finite-degree-fillings: that theorem is the matrix stable-range branch; the present theorem combines it with every diffuse finite factor in the replication range needed for gap traces.
  stw22-diffuse-weighted-copy-all-finite-sphere-fillings: that theorem assumes every factor is diffuse; the present theorem permits arbitrary matrix, diffuse, and mixed finite-factor values.
  stw22-half-slack-all-factor-weighted-copy-uniform-s4-fillings: that theorem stops in degree four; the present theorem treats every fixed finite degree with a degree-dependent matrix modulus.
artifacts:
  - research/artifacts/stw22-all-factor-finite-dimensional-breakthrough-2026-08-31.md
---

Fix an integer `j>=2` and put

```text
t=floor((j-1)/2),
C_j=j+1+t(t+1)/2+floor(j/2).                           (AFD-1)
```

Let `(N,tau)` be any finite factor with separable predual, let

```text
m>=ceil(j/2),       0<=a<=1,       m tau(supp(a))<=1/2. (AFD-2)
```

Then the Hilbert-sum weighted-copy fibre `F_(N,m)(a)` is globally
`j`-connected. Every continuous `S^j` contained in the ball of radius

```text
rho_AF,j(epsilon)
 =min{epsilon_0^3/216000000,
      epsilon_0^3/(276480 C_j)},   epsilon_0=min(epsilon,1), (AFD-3)
```

about one point extends over `B^(j+1)` inside the concentric
`epsilon`-ball.

For each fixed finite `j`, these fibres form a uniformly equi-`LC^j`
family over all factor types, matrix sizes, II1 isomorphism classes,
replication numbers satisfying (AFD-2), and weights. The assertion is
degreewise: neither the threshold nor a positive modulus is claimed
uniform as `j` tends to infinity.
