---
rg: 2
id: ah-algebras-realize-ranks-approximately
kind: claim
title: Rank functions are uniformly dense in the continuous affine functions on the trace simplex of every simple unital AH algebra
distinct_from:
  simple-ah-strict-comparison-is-z-stable: that is the Toms--Winter conclusion for AH algebras with strict comparison; this is the comparison-free density of ranks that feeds one proof of it.
  stw23-finite-extreme-trace-boundary-has-all-ranks: that realizes every rank exactly under finitely many extreme traces; this only approximates continuous affine functions, but on every AH algebra with no tracial hypothesis.
  thiel-stable-rank-one-ranks-close-purity-with-comparison: that realizes all ranks exactly under stable rank one; this approximates continuous ranks with no stable rank hypothesis, only AH structure.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

Let `A` be a unital simple separable infinite-dimensional AH algebra.  For
every continuous strictly positive affine function `f` on `T(A)` and every
`eta > 0` there is a positive element `y in M_infty(A)` with

```text
|d_tau(y) - f(tau)| < eta     for every tau in T(A).
```

No stable rank one, strict comparison, or dimension growth hypothesis is
used.  Call this property rank density (RD).  It is strictly weaker than exact
realization of ranks (STW Problem XXIII).
