---
rg: 2
id: radical-collision-criterion-proof
kind: route
title: Pass to the detecting range of a sofic-invisible element
target: radical-collision-criterion
requires: []
artifacts:
  - GroupApproximation/Sofic/HyperlinearResidualDetector.lean
  - GroupApproximation/Sofic/RadicalSeparation.lean
---

This range argument is kernel-checked as
`hyperlinear_range_and_failureOfSoficity_of_soficInvisible` and its
existential wrapper.  `RadicalSeparation.lean` records the equivalent
residual non-containment formulation.  No analytic permanence theorem is
used beyond the definition of a hyperlinear target and closure under
subgroups.
