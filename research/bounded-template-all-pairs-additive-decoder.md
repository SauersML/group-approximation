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

The analytic requirement has now been reduced further.  The route
`average-blr-self-correction-narrows-bounded-template-decoder` proves that it
is enough for the occurrence layer to recover the average dense BLR energy
`(BTA1)`: unitary polar self-correction then gives `(BAT1)` with no
commutativity assumption.  Thus `bounded-template-average-blr-occurrence-decoder`
is the weakest remaining gate in this lane.

## Attempts

- **Dense BLR.**  It directly tests all additive pairs, but its complete
  triangle incidence is not bounded-template.
- **Expander clouds plus local BLR.**  Equality synchronization recreates
  the two-pair contour obstruction.
- **Equality clouds with one distinguished mixed port.**  In a bounded-degree
  equality fiber of size `m`, change only the distinguished port by a constant
  HS distance.  Only `O(1)` equality edges fail, so normalized equality defect
  is `O(1/m)`, while the mixed observable at that port changes by a constant.
  Giving the mixed test uniform access to all ports needs `Omega(m)` lifted
  pair edges; any two lifts of one logical pair create the fatal contour of
  `equality-synchronized-lifts-create-two-pair-contours`.
- **Only average additive error.**  This is no longer an analytic obstruction:
  `unitary-blr-average-self-corrects-uniformly` upgrades average BLR error to
  a uniform almost-action.  Producing that average from bounded-template
  non-equality occurrences remains open.
