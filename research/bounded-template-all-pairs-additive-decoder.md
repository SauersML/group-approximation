---
rg: 2
id: bounded-template-all-pairs-additive-decoder
kind: claim
title: Decode bounded-template same-basis occurrences to an all-pairs additive table
---

OPEN.  Construct a bounded-degree, bounded-template, perfect-completeness
occurrence test for a table `f:F_2^n->U(d)` such that test defect `epsilon`
implies, on one common positive-mass carrier,

```text
max_(x,y) ||f(x)f(y)-f(x+y)||_2 <= C epsilon^theta             (BAT1)
```

after changing the table by at most `C epsilon^theta` in normalized HS norm.
The constants must be independent of `n,d`, and the incidence must not use
repeated equality fibers forbidden by the balanced/relative
small-cancellation placement audit.

By `finite-abelian-hs-almost-actions-round-in-the-same-dimension`, `(BAT1)`
is enough to round in dimension `d`; no additional finite-group stability
theorem is missing.

## Attempts

- **Dense BLR.**  It directly tests all additive pairs, but its complete
  triangle incidence is not bounded-template.
- **Expander clouds plus local BLR.**  Equality synchronization recreates
  the two-pair contour obstruction.
- **Only average additive error.**  The available same-dimension proof uses
  the all-pairs Gowers--Hatami hypothesis.  A direct average-error version
  could replace `(BAT1)`, but has not been proved here.

