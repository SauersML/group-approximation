---
rg: 2
id: atlas-o8plus-seam-proof
kind: route
title: Classify singular-parabolic Q1920 slices and test both Omega8+(2) embedding twists
target: atlas-o8plus-canonical-moved-module-completion-fails
requires:
  - atlas-moved-modules-have-a-forced-v4-bridge
artifacts:
  - experiments/atlas_a4_q1920_o8p_discovery.g
  - research/artifacts/atlas-a4-q1920-o8plus-seam.json
---

The verifier constructs the two nonzero-vector orbits of lengths 135 and
120 in the natural eight-dimensional module and selects the singular orbit.
Exact 2-core and complement computations identify its stabilizer as the
order-1290240 group `2^6:A8`.  Enumerating `A5` classes and invariant
five-dimensional radical submodules proves uniqueness in `(O8P-1)`.

As in the Sp6 audit, right cosets of the ambient-induced automorphism group
inside `Aut(Q)` classify all embedding twists.  For both twists and both
marked tuples the verifier computes the whole pointwise `A` centralizer and
evaluates the literal collision word, `(ct)^3`, and faithful `S4` order and
structure.  The four zero counts in `(O8P-2)` are therefore exhaustive for
this canonical orthogonal host.
