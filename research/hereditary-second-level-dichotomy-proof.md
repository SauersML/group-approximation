---
rg: 2
id: hereditary-second-level-dichotomy-proof
kind: route
title: The two isomorphism types of the switch, and the two forms of transport
target: hereditary-property-second-level-dichotomy
requires:
  - arbitrary-forbidden-seed-hereditary-property-switch
---

The parametric switch seeded by a finite presentation code of `D` has
value `1` on `INF` and `D` on `FIN`.  Under (I), transport `P(1)` across
the isomorphism on the `INF` branch and contradict `¬P(D)` on the `FIN`
branch; under (H), heredity gives isomorphism invariance for free.  Since
`INF` is `Pi^0_2`-complete and the compiled code is computable in the
source code, (HD1) follows; complements give the `Sigma^0_2` statement.
Both forms are kernel-checked, in
`Computability/SoficRecognitionSecondLevel` and
`Computability/IsoInvariantSwitchHardness`.
