---
rg: 2
id: soft-transport-thresholds-to-hall-subsequence
kind: claim
title: On a fixed finite Fourier alphabet, a vanishing-cost positive-dual transport certificate yields a hard Hall-deficient subsequence
---

Let `V,W` be fixed finite sets with positive source and target weights
`alpha_v,beta_u` of equal total mass.  For each `n`, let `mu_n(u,v)` be a
transport plan with those marginals.  Suppose there are costs

```text
0 <= c_n(u,v) <= 1
```

and transport-dual potentials `x_n(v),y_n(u)` satisfying

```text
x_n(v)+y_n(u) <= c_n(u,v),
sum_v alpha_v x_n(v)+sum_u beta_u y_n(u) >= gamma>0,   (STH1)
```

while

```text
sum_(u,v) c_n(u,v) mu_n(u,v) -> 0.                    (STH2)
```

Then there are a subsequence `n_j`, one fixed bipartite graph
`E subset W x V`, and one source set `S subset V` such that

```text
alpha(S) > beta(N_E(S))                               (STH3)
```

and

```text
sum_((u,v) notin E) mu_(n_j)(u,v) -> 0.              (STH4)
```

Thus on a fixed finite block alphabet, an asymptotic soft transportation gap
always contains a hard weighted-Hall support obstruction after passing to a
subsequence.  The costs remain useful as an optimization/search language,
but they do not remove the finite-coordinate support-selection gate.