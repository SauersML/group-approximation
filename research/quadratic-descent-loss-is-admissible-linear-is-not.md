---
rg: 2
id: quadratic-descent-loss-is-admissible-linear-is-not
kind: claim
title: A descent operation may lose accuracy quadratically but not by a constant factor
distinct_from:
  dimension-descent-criterion-for-non-mf: that is the criterion, which asks the operation to preserve one fixed threshold; this is the accounting that says which loss rates can preserve it and which cannot.
  full-mf-radical-linear-relator-inequality: that is an inequality between the generator displacement and the relator defect in a single model; this compares the defects of two models related by a descent step.
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

In the setting of `dimension-descent-criterion-for-non-mf`, suppose the
operation satisfies

```text
delta(V) <= C delta(U)^2.
```

Then any `epsilon_0 < 1/C` is preserved by every descent step, and iterating
drives the defect to zero quadratically.  So a quadratic loss is admissible.

A constant multiplicative loss is not.  If only `delta(V) <= K delta(U)` with
`K > 1` is available, then `d` descent steps cost a factor `K^d`, so
admissibility would need the starting defect below `epsilon_0 K^(-d)`.  MF
approximation supplies defects tending to zero with no control of the rate
against the dimensions, which may grow arbitrarily fast, so no such starting
tuple is guaranteed.

The design target for any construction is therefore error correction, not
merely dimension reduction.
