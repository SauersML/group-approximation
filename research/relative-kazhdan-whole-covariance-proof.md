---
rg: 2
id: relative-kazhdan-whole-covariance-proof
kind: route
title: Project the transporter to the M-fixed subspace
target: relative-kazhdan-bimodule-upgrades-finite-covariance
requires: []
---

The relative Kazhdan inequality gives an `M`-fixed vector `eta` with

```text
||xi-eta||_2 <= epsilon/kappa.
```

For every `m in M`, unitarity and `Theta_s(m)eta=eta` imply

```text
||Theta_s(m)xi-xi||_2
 <= ||Theta_s(m)(xi-eta)||_2+||eta-xi||_2
 <= 2 epsilon/kappa.
```

Substitute `(RKU1)` and `xi=pi(s)` to obtain `(RKU2)`.  Multiplying on the
right by `pi(s)^*` gives the usual covariance defect

```text
||pi(s)rho(m)pi(s)^*-rho(s m)||_2.
```

The estimate is uniform in `m` and in the matrix dimension.  Finally
`infinite-character-actor-word-energy-interface`, equations `(IWE2)--(IWE5)`,
turns this supremum into the fine PVM transport energy.

