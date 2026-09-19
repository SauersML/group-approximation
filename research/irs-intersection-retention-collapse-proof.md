---
rg: 2
id: irs-intersection-retention-collapse-proof
kind: route
title: Intersect countably many IRS samples and pass measure domination to the Dirac limit
target: irs-intersection-fixed-weight-retention-collapses
requires: []
---

For each `g`, independence gives

```text
Prob(g in K^(n))=Prob(g in K_1)^n.
```

If this one-point probability is less than one, the probability that `g`
survives every intersection is zero.  Countability of `G` therefore shows
that the decreasing intersection of all `K_i` equals `H` almost surely.
Decreasing subgroups converge in the Chabauty topology to their intersection,
which proves `(IIR1)`.

Equation `(IIR2)` says `mu_n-beta mu` is a positive measure.  Positivity is
weak-star closed, so `(IIR1)` gives

```text
delta_H-beta mu >= 0.
```

Every Borel set disjoint from `{H}` consequently has `mu`-measure zero.
Thus `mu` is supported at `H`, and normalization gives `mu=delta_H`.

