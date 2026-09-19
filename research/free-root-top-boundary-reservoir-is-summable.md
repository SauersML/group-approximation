---
rg: 2
id: free-root-top-boundary-reservoir-is-summable
kind: claim
title: Free-root top-degree character layers have unit total mass capacity
artifacts:
  - GroupApproximation/PropertyT/FreeRootCharacterValuation.lean
distinct_from:
  alternating-free-ring-shears-have-strict-degree-drift: that gives distinct leading polynomial degrees for the proposed transporter; this proves the corresponding finite-stage Fourier boundary layers have a uniform summable mass budget in every orthogonal representation.
  first-hit-carrier-contraction-ladder: that is an abstract scalar ledger assuming summable exits; this constructs exactly such a summable reservoir from free-root character valuation.
  one-sided-paired-frame-reverse-reservoir-collapse: that must still identify the paired frame's emitted 011 carrier with these boundary layers and preserve its baseline packet copy.
---

Let `rho` be any orthogonal representation of
`EL_3(F_2<X>)`, let `z` be any vector, and use either coordinate of one
finite free-root coefficient plane.  Write `m_n` for the squared Fourier mass
of characters still trivial through degree `n`, and `b_(n+1)` for the mass of
characters first detected in degree `n+1`.  Then, for every `N`,

```text
m_n = b_(n+1) + m_(n+1),                               (FRS1)
sum_(0<=n<N) b_(n+1) = m_0-m_N <= m_0 <= ||z||^2.      (FRS2)
```

Both statements hold separately for the first and second plane coordinate.
They are dimension-free and require no asymptotic limit.  For a unit vector,
the entire infinite family of new degree layers therefore has capacity at
most one.

This is the exact substitute for explicitly constructing pairwise orthogonal
prefix projections.  The Fourier components at one fine stage are orthogonal,
and `(FRS1)` tracks the refinement differences across stages; `(FRS2)` is the
finite normalized-mass inequality needed by `(FHC3)`.
