---
rg: 2
id: full-pair-routing-of-complete-baseline-prefix-capacity-proof
kind: route
title: Compare the largest full-pair companion with the unused successor-prefix capacity
target: full-pair-routing-of-complete-baseline-has-a-prefix-capacity-gap
requires:
  - full-index-two-hnn-edge-creates-own-prefix-split
---

For each retained type, the full-pair Reynolds identity supplies an
equal-trace companion in the negative `B` sector.  One of the fixed `T`
retained types has at least `1/T` of the complete baseline mass.  Its
companion alone therefore occupies that much negative-prefix capacity.
Every successor carrier lies in the orthogonal positive-prefix sector, so it
must lose the same amount.  The approximate inequality follows by inserting
the three fixed `O(sqrt(E))` errors before this pigeonhole argument.
