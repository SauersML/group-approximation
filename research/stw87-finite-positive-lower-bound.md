---
rg: 2
id: stw87-finite-positive-lower-bound
kind: claim
title: Finite asymptotic dimension at least two lower-bounds uniform Roe nuclear dimension
artifacts:
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
---

For every countable discrete bounded-geometry metric space `X` with
`2 ≤ asdim(X) < ∞`, prove

```text
asdim(X) ≤ dim_nuc(C*_u(X)).
```

## Attempts

The subspace-corner theorem propagates any known lower-bound seed, but no seed
of value at least two is produced here; `X=ℤ²` is already an unresolved seed.
Li--Liao--Winter identify asymptotic dimension with diagonal dimension, but
their comparison has the opposite direction.  Postcomposing arbitrary
nuclear-dimension return maps with the diagonal expectation cannot repair the
direction because that expectation destroys order zero in a two-point matrix
corner.  A solution therefore needs either a new nuclear lower-bound invariant
or a structured diagonal-recovery theorem, not raw expectation averaging.
