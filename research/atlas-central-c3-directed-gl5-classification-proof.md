---
rg: 2
id: atlas-central-c3-directed-gl5-classification-proof
kind: route
title: Exact directed-central constraint and GL5 orbit-screen proof
target: atlas-central-c3-directed-gl5-classification
requires: []
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas_a4_gl5_core_collision_countermodel.py
  - research/artifacts/atlas-a4-central-c3-directed-gl5-classification.json
---

## Constraint decomposition

The packet generator reconstructs all thirty shortest pair-cubes.  Select the
two nonidentity elements of the center of `H_18~=S3 x C3`.  Exactly sixteen
word occurrences contain one of them.  Canonicalizing each occurrence by its
ordered pair of factor-one and factor-two matrices leaves eight keys.  The
keys are the cartesian products `Z x B` and `B x Z`, with two occurrences per
key, proving `(A4-C3-DIR)` and the two directed `K_(2,2)` decomposition.

## Exhaustive finite classification

`atlas_a4_gl5_packet_screen.py --core --central-singleton-survivors` writes
every element of `GL_5(F2)` uniquely as one of 496 representatives for
`GL_5/GL_4` times one of 20,160 internal alignments.  Conjugacy-class masks
first impose all eight distinct core relations.  On every surviving matrix,
exact binary multiplication then tests collision `19243` and the eight
ordered central constraints.  The four masks and counts in `(A4-C3-GL5)` sum
to 216; no floating-point comparison is used.

Finally `atlas_a4_gl5_core_collision_countermodel.py --certificate reverse22`
substitutes `(A4-C3-HALF)` directly into the original thirty packet words.  It
checks the fourteen core occurrences, the eight `D_21` occurrences, collision
identity, and nontrivial covariance on each of the eight named rank-three
generators.  This independently verifies the displayed half completion.
