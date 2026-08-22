---
rg: 2
id: atlas-l44-subfield-packet-collision-exclusion
kind: claim
title: The augmented Atlas packet excludes the L4(4) subfield A8 equality case
artifacts:
  - experiments/atlas_a4_l44_fan_escape.py
distinct_from:
  atlas-l44-local-packet-fans-do-not-force-subfield-support: that proves the local fan and H6-only shortcuts fail; this asks for the common-frame coupling of both packet components and collision.
---

For the standard subfield chart `A=GL4(2)<L4(4)`, classify the marked
conjugate charts `B` which satisfy all twelve distinct packet edges.  Prove
that collision `19243` (or q14) excludes every packet survivor that generates
`L4(4)`.

The exact local reduction is now small at its first stage: an `H6` generator
pair has only `1262` ordered packet-compatible images.  What remains is to
couple each such pair to the `H18` component through the same ambient
conjugator-centralizer fiber.  A capped direct implementation did not finish,
so no full-packet survivor count is asserted here.

## Attempts

- One-vertex support recognition fails exactly: the two fan fibers have `336`
  and `150` points, with nonsubfield points in both.
- Coupling the full `H6` rectangle leaves `1262` ordered pairs.  Iterating its
  common-conjugator centralizer fibers against `H18` did not finish within the
  strict two-minute development cap.  The next attack should quotient those
  fibers by the centralizer action before replay, not extend the raw loop.
- `atlas-l44-h6-has-thirty-frobenius-frames` supplies that quotient exactly:
  each liftable pair has thirty candidate subfield forms and six internal
  labelings, while a compatible `H18` placement determines the common lift
  uniquely up to scalar.  The remaining screen must first discard
  non-liftable rectangle pairs, then test this `30 x 6` factored fiber.
