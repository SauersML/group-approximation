---
rg: 2
id: plancherel-matrix-index-deletion-bound-proof
kind: route
title: The canonical transport charges every lost Hall neighbor to a deleted edge
requires:
  - plancherel-restriction-coupling
target: plancherel-matrix-index-deletion-bound
---

For a fixed source vertex `(sigma,a)`, summing `(PMD1)` over all target
matrix indices gives

```text
sum_(theta,b) Pi((sigma,a),(theta,b))
 = (1/|G|) sum_theta d_theta m_(sigma,theta)
 = d_sigma/|G|,
```

using the dimension identity from `plancherel-restriction-coupling`.  For a
fixed target vertex `(theta,b)`, Frobenius reciprocity similarly gives

```text
sum_(sigma,a) Pi((sigma,a),(theta,b))
 = (1/|G|) sum_sigma d_sigma m_(sigma,theta)
 = [G:H] d_theta/|G|
 = d_theta/|H|.
```

So `Pi` has the required marginals.

Fix a source set `S` and abbreviate `N=N_E(S)`.  Marginality gives

```text
w(S)=Pi(S x all),
w(N)=Pi(all x N).
```

Hence

```text
Delta_E(S)
 = Pi(S x all)-Pi(all x N)
 <= Pi(S x (all\N)).                                  (P1)
```

Every full-branching edge from a vertex in `S` to a vertex outside `N` must
have been deleted; otherwise its target would lie in `N_E(S)`.  Therefore the
support of `Pi` inside `S x (all\N)` is contained in `F`, and `(P1)` yields

```text
Delta_E(S)
 <= Pi(F intersect (S x (all\N)))
 <= Pi(F).
```

Taking the maximum over `S` proves `(PMD3)` and `(PMD4)`.
