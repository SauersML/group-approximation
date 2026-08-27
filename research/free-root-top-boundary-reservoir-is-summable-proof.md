---
rg: 2
id: free-root-top-boundary-reservoir-is-summable-proof
kind: route
title: Telescope the machine-checked trivial-mass refinement identity
target: free-root-top-boundary-reservoir-is-summable
requires: []
artifacts:
  - GroupApproximation/PropertyT/FreeRootCharacterValuation.lean
---

The existing Fourier refinement theorem proves `(FRS1)` as
`planeFirstTrivialMass_step` and `planeSecondTrivialMass_step`.  Induction on
`N`, using `Finset.sum_range_succ`, gives the two exact finite telescoping
identities

```text
sum_planeFirstTopBoundaryMass_range_eq,
sum_planeSecondTopBoundaryMass_range_eq.
```

The residual masses `m_N` are sums of squares and hence nonnegative.  Finally,
each `m_0` is the sum over a subset of the complete finite-plane Fourier
decomposition, while `sum_norm_planeComponent_sq` identifies the full sum
with `||z||^2`.  This gives the two bounds

```text
sum_planeFirstTopBoundaryMass_range_le_norm_sq,
sum_planeSecondTopBoundaryMass_range_le_norm_sq.
```

All four new statements elaborate against the Lean kernel.  The remote check
used the existing warm dependency build, one low-priority process, and no
new package build.
