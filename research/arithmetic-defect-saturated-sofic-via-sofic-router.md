---
rg: 2
id: arithmetic-defect-saturated-sofic-via-sofic-router
kind: route
title: Feed a sofic-preserving marked router into the arithmetic saturation sandwich
target: arithmetic-defect-saturated-kazhdan-group-is-sofic
requires:
  - sofic-preserving-single-defect-kazhdan-router
  - arithmetic-single-defect-saturation
  - normal-kazhdan-defect-non-mf
---

Apply the router to the concrete arithmetic source and its certified word
`sigma`.  Its output is sofic by `(SPR1)`.  The normal-generation identity
and functoriality place the full intrinsic defect between
`<<q(sigma)>>^Q=Q` and `Q`, so it is all of `Q`.  The remaining clauses of
`(ADS1)` are exactly the router's torsion-free, finite-presentation,
property-`(T)`, nontriviality and survival guarantees.

The normal-Kazhdan theorem then proves that this sofic `Q` has full MF
radical, confirming that the router cannot be replaced by a residually finite
one.

