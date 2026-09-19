---
rg: 2
id: atlas-q1920-holomorph-seam-proof
kind: route
title: Enumerate the pointwise radial centralizer in Hol(Q1920) and evaluate the collision words exactly
target: atlas-q1920-holomorph-has-no-collision-involution
requires:
  - atlas-q1920-is-radial-holonomy-extension
artifacts:
  - experiments/atlas_a4_q1920_automorphism_seam.g
  - research/artifacts/atlas-a4-q1920-holomorph-seam.json
---

For both markings GAP computes `|Aut(Q)|=7680`; the pointwise stabilizer of
`A` in `Aut(Q)` has order four and element-order profile `1,2,2,2`.

Every element of `Hol(Q)` is stored exactly as an affine pair `(q,alpha)`.
If it centralizes `A`, its induced conjugation on `Q` belongs to that
four-element pointwise stabilizer.  Conversely this observation recovers all
7,680 pointwise-centralizing affine pairs.  The verifier checks pair
multiplication, squares, and the two literal words in `(Q1920-HOL-1)` for
each one.  The complete order histogram and solution count are preserved in
the JSON artifact.  Both marked computations return only the identity.
