---
rg: 2
id: atlas-sp6-seam-proof
kind: route
title: Transport both marked Q1920 tuples through every canonical Sp6(2) embedding twist
target: atlas-sp6-canonical-moved-module-completion-fails
requires:
  - atlas-any-q1920-completion-must-move-the-module
artifacts:
  - experiments/atlas_a4_q1920_sp6_seam.g
  - research/artifacts/atlas-a4-q1920-sp6-seam.json
---

The verifier constructs `Sp(6,2)` and its order-23040 point stabilizer,
checks that its 2-core is elementary abelian of order 32, and enumerates the
two `A5` classes in a Levi complement.  The module conjugacy-class test
`(SP6-1)` selects one class exactly.

GAP then computes the normalizer of this `Q`, its full automorphism group,
and the four right cosets of the induced normalizer-automorphism subgroup.
These cosets are precisely the ambient-conjugacy-inequivalent embeddings of
an abstract marked `Q` onto the fixed parabolic slice.  For each twist, the
literal collision word, the cubic `(ct)^3`, and the exact subgroup order and
structure `S4` are checked.  No twist supplies even the collision
involution, proving `(SP6-2)` before the seam generator `z` is considered.
