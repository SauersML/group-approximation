---
rg: 2
id: stw99-xcix-centrality-window-collapse-proof
kind: route
title: Make the source copy arbitrarily central before one quantitative transport
target: stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance
requires:
  - stw99-xcix-central-copy-transfer-bound
---

Fix contractions `x_1,...,x_m in B` and choose contractions `a_i in A` with
`||a_i-x_i||<gamma`.  Since `A` is Z-stable, for every `eta>0` there is a
unital embedding `rho:Z->A` such that

```text
max_(i<=m,j<=k) ||[rho(z_j),a_i]|| < eta.
```

Apply `stw99-xcix-central-copy-transfer-bound` with
`X={x_1,...,x_m}` and `Y={z_1,...,z_k}`.  It gives an embedding
`psi:Z->B` with

```text
max_(i,j) ||[psi(z_j),x_i]||
 < eta+304 sqrt(gamma)+2 gamma.
```

The estimate at `1_Z` makes `psi` unital, as in
`stw99-xcix-z-saturated-limit-proof`.  First take the infimum over `psi`,
then let `eta` decrease to zero, and finally take the supremum over all
contraction `m`-tuples.  This proves `(CW)`.  Applying `(CW)` coordinatewise
when `gamma_n->0` proves the last assertion.
