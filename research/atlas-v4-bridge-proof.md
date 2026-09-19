---
rg: 2
id: atlas-v4-bridge-proof
kind: route
title: Conjugate the radial module mismatch through the marked collision S4
target: atlas-moved-modules-have-a-forced-v4-bridge
requires:
  - atlas-any-q1920-completion-must-move-the-module
artifacts:
  - experiments/atlas_a4_q1920_module_structure.g
  - experiments/atlas_a4_large_k22_intersection_screen.g
  - research/artifacts/atlas-a4-q1920-module-structure.json
  - research/artifacts/atlas-a4-large-k22-intersection-screen.json
---

The module verifier identifies the mismatch involutions as the third labeled
pair, proves their product has order two, and computes an order-eight
`A`-span.  The collision calibration maps that `B` label to the third
transposition, whose conjugate by `c` is disjoint.  Substitution gives the
two commuting identities in `(V4-BRIDGE-2)`.  Nontriviality of the resulting
Klein four follows because `v=v^c` would imply `d=d^c`, contradicting the
same collision centralizer calibration.
