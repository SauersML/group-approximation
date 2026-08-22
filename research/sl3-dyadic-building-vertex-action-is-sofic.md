---
rg: 2
id: sl3-dyadic-building-vertex-action-is-sofic
kind: claim
title: The dyadic SL3 Bruhat--Tits type-zero vertex action is sofic
distinct_from:
  dyadic-bruhat-tits-vertex-action-is-sofic: that is the rank-one PSL2 action with an amalgam/random-lift route; this is the rank-two SL3 action with Kazhdan stabilizer.
  sl3-regular-double-collapse-forces-nonsofic-vertex-action: that proves a conditional consequence in the opposite direction; this is the action-soficity proposition itself.
---

For

```text
A=SL_3(Z[1/2]),   C=SL_3(Z),
```

the transitive action `A action A/C`, equivalently the action on the
type-zero vertices of the `SL_3(Q_2)` affine building, is sofic in the
Gao--Kunnawalkam Elayavalli--Patchell sense.

## Attempts

Finite building quotients and random lifts are the natural models, but
`sl3-finite-building-quotients-forget-arithmetic-labels` proves that their
unlabelled local geometry does not retain the fixed dense arithmetic
labels.  The concrete remaining construction is
`sl3-building-deck-cocycles-round-coherently`.  Co-density of `C` in finite
quotients blocks exact quotient models but does not decide approximate
sofic action models, so neither sign is currently established.
