---
rg: 2
id: phase-safe-toric-via-projective-kernel
kind: route
title: Mine a predicate phase in the tracial projective kernel and compile the toric gap
target: phase-safe-toric-gap-game-exists
requires:
  - mipstar-bcs-tracial-nonru-exists
  - boolean-predicate-central-phase-word
  - bcs-projective-kernel-phase-compilation
  - gowers-hatami-finite-group-hs-stability
---

Use the finite `2`-group word as the scalar phase register and the engineered
tracial model for perfect completeness.  Finite-group flexible stability
prevents approximate packet tables from faking the local phase.  The robust
non-RU gap gives finite-dimensional soundness, while the full tracial model
certifies that the phase is not killed by normal closure.  These are exactly
the three clauses of the target toric game.

This route counts violations rather than excluding forbidden selector
characters, so it does not invoke the finite-selector induction barrier.
