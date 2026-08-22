---
rg: 2
id: atlas-full-kernel-strata-rank-separation
kind: claim
title: Separate the full collision-zero and q14-zero packet strata in normalized rank
distinct_from:
  atlas-m2-kernel-phases-have-rank-path-barrier: that proves separation only for the two pure amplified m2 endpoints and isolates the general defect minima; this asks for a uniform estimate on every packet-zero multiplicity gauge.
  atlas-augmented-rank-zero-set-compactness: that promotes an arbitrary joint approximate zero to one exact finite zero; this is the narrower one-sided exact-stratum distance problem.
---

OPEN.  With `C_m,H_m,alpha_m,beta_m` as in
`atlas-m2-kernel-phases-have-rank-path-barrier`, prove that at least one of

```text
inf_m alpha_m/m>0,
inf_m beta_m/m>0                                      (FSR1)
```

holds.  By `(RPB7)` this gives a dimension-independent normalized-rank gap
between the full packet-zero collision and q14 strata.

## Attempts

- The exact m2 slice gives ranks one and two, but it is not an exhaustive
  classification of all packet-zero gauges and supplies no scaling law.
- Direct sums of its two phases preserve positive defect density and the
  upper-Toeplitz theorem preserves it under flag couplings.  Neither controls
  non-flag-preserving new bulk phases.
- Bounded-rank paths themselves are not an obstruction: `(RPB3)` connects the
  pure phases with rank-eight steps.  A useful invariant must bound the
  endpoint word defect throughout an entire exact zero stratum, rather than
  merely distinguish connected components.
- Fixed rank congruences cannot prove `(FSR1)` because amplification clears
  them.  A viable invariant must be a normalized noncommutative-rank or
  shrunk-subspace quantity stable under arbitrary matrix blow-up.
- `atlas-separate-chart-module-ledger-is-kernel-blind` removes the complete
  separate-chart module ledger, not merely congruences: the H6/H18/A4/A8
  restrictions, their fixed spaces, commutants, composition factors, and
  extension classes are independent of the relative gauge and hence agree
  on both zero strata.  The first remaining additive rank-Lipschitz
  candidates are mixed intersection dimensions
  `dim(Fix_K intersect T^-1 Fix_L)` or equivalent cross-chart
  extension/holonomy modules.  No kernel-sensitive inequality for one of
  these mixed coordinates is currently known.
