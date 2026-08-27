---
rg: 2
id: atlas-o8minus-seam-proof
kind: route
title: Classify singular-parabolic Q1920 slices and test both Omega8-(2) embedding twists
target: atlas-o8minus-canonical-moved-module-completion-fails
requires:
  - atlas-moved-modules-have-a-forced-v4-bridge
artifacts:
  - experiments/atlas_a4_q1920_o8m_discovery.g
  - research/artifacts/atlas-a4-q1920-o8minus-seam.json
---

The verifier constructs the natural eight-dimensional module, whose nonzero
vector orbits have lengths 119 and 136.  The 119-point stabilizer has the
required elementary abelian 2-core of order64.  Exact complement, subgroup,
and invariant-submodule calculations identify one matching Q1920 class.

Right cosets of the ambient-induced automorphism subgroup inside `Aut(Q)`
give two embedding twists.  For both twists and both exact marked tuples the
whole pointwise `A` centralizer is enumerated and the literal collision
relations plus faithful `S4` structure are checked.  All four searches give
zero collision involutions, proving `(O8M-1)`.
