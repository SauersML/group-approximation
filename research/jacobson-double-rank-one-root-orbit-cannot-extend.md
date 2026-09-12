---
rg: 2
id: jacobson-double-rank-one-root-orbit-cannot-extend
kind: claim
title: Two-dimensional first-root character fibers also fail the shared Jacobson multiplicity constraints
distinct_from:
  jacobson-single-rank-one-root-orbit-cannot-extend: that excludes one-dimensional fibers; this excludes two-dimensional fibers, including both possible rank-one and rank-two boundary support profiles.
artifacts:
  - research/artifacts/jacobson-double-rank-one-orbit-obstruction-2026-09-08.md
---

Let the finite first-level packet `P=N semidirect F` and boundary
packet `J` be represented exactly on the same dimension and agree on
their specified intersection `I`. Suppose the head mark survives and
`||(hb)^3-I||<2`. Then their nontrivial `N`-character support cannot
be exactly the rank-one orbit with two-dimensional fibers, even with
an arbitrary `N`-trivial complement.

Together with the one-dimensional-fiber exclusion, this implies that
every exact head-retaining representation of `Xi` has dimension at
least 147. Coherent correction gives the explicit estimate

```text
max(||W-I||,||(hb)^3-I||)>1/18,259,771,392
```

for exact compatible `F,J` representations retaining the head on
dimensions at most 146. The unrestricted matrix infimum remains open.

DERIVATION
jacobson-double-root-fiber-sign-standard-proof
