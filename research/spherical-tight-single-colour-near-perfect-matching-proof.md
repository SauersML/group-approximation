---
rg: 2
id: spherical-tight-single-colour-near-perfect-matching-proof
kind: route
title: Uniform bipartite degrees plus Konig edge colouring give a large matching
target: spherical-tight-single-colour-near-perfect-matching
requires: []
---

Let `p=p_(d,rho)>0` be the Haar measure of a radius-`rho` ball about one
unit vector.  Conditional on `x_i`, the `N-1` off-diagonal indicators

```text
1[||U x_i-x_j||<=rho],  j != i,
```

are independent Bernoulli variables of mean `p`; the diagonal contributes
one extra bounded summand.  The same statement holds for every right degree,
conditioning instead on `x_j` and using

```text
||U x_i-x_j||=||x_i-U^*x_j||.
```

Choose `eps_N->0` with `N p eps_N^2 >> log N`.  Chernoff and a union bound
show that all left and right degrees lie between

```text
(1-eps_N)Np  and  (1+eps_N)Np
```

up to a negligible additive diagonal term, with probability `1-o(1)`.
Write these bounds as `delta_N` and `Delta_N`.

A finite bipartite graph has edge-chromatic number equal to its maximum
degree.  Hence its edges split into `Delta_N` matchings.  Since the graph has
at least `N delta_N` edges, one matching has size at least

```text
N delta_N / Delta_N = (1-o(1))N.
```

For finitely many colours, take the intersection of the corresponding
probability-one-asymptotic degree events and choose one large matching in
each colour graph.
