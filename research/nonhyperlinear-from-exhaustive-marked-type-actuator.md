---
rg: 2
id: nonhyperlinear-from-exhaustive-marked-type-actuator
kind: route
title: Sum exhaustive marked-type energy and apply the static finite-game gap
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - dihedral-spin-packet-supplies-common-partial-swap
  - common-source-partial-isometries-decode-one-game-state
  - exhaustive-marked-type-energy-summation
  - finite-matrix-only-exhaustive-marked-type-actuator
---

Exact completeness supplies a representation with the central D8 mark
`y!=1`.  If the resulting group were hyperlinear, canonical matrix
microstates would exactify the fixed context packets and have marked mass

```text
tr((1-y)/2)->1/2.
```

The finite-matrix actuator supplies the typewise estimates `(EMT2)`.
`exhaustive-marked-type-energy-summation` sums them over every marked type
without a carrier-alignment loss.  Literal consistency commutators and the
common-source finite-game inequality then give a fixed positive relator
energy proportional to the marked mass.  This contradicts the vanishing
defect of the canonical microstates.
