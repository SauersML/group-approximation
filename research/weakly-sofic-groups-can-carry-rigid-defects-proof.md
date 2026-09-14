---
rg: 2
id: weakly-sofic-groups-can-carry-rigid-defects-proof
kind: route
title: The weakly sofic Kun--Thom wreath has a nontrivial rigid defect
target: weakly-sofic-groups-can-carry-rigid-defects
requires: [weakly-sofic-not-sofic, kun-thom-wreath-carries-rigid-defect]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

`weakly-sofic-not-sofic` proves `W` weakly sofic: Glebsky's
residually-finite-by-weakly-sofic permanence, applied to the lamp kernel and
the residually finite actor.
`kun-thom-wreath-carries-rigid-defect` computes a nontrivial rigid defect in
the same `W`.

The normalization failure then follows from the `not DD <=> not NORM`
equivalence, where property (U) holds by definition of weak soficity. It is
recorded in the claim body, not as a separate prerequisite.
