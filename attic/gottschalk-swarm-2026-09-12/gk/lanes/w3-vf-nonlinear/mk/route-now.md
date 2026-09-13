---
rg: 2
id: linearly-dirty-ancilla-words-affine-proof
kind: route
title: Track the dirt part of the data functional of a linearly dirty state; linear moves fix it and exact reads only add constants
target: linearly-dirty-ancilla-words-realize-only-affine-data-maps
requires: []
artifacts:
  - research/artifacts/marker-ancilla-linear-dirt-invariant-2026-09-12.md
---

Section 2 of the artifact.
- **Representation independence.** Whether `Q` is affine does not depend on the representation (step 2).
- **Linear moves.** They fix `Q`, and constant translations add constants (step 3).
- **Exact reads.** When `c_T != 0` the read is constant, by the adjugate formula and the surjectivity of
  nonsingular linear automata (Lemma A, step 4).
- **End.** At a realization the ancilla columns of `M` are `(0; I)`, so `Q = a^(-1) F - x` (step 5).
- **Corollary.** `tau` is not affine.
