---
rg: 2
id: phase-safe-toric-via-projective-kernel
kind: route
title: Mine a predicate phase in the tracial projective kernel and compile the toric gap
target: phase-safe-toric-gap-game-exists
requires:
  - mipstar-bcs-tracial-nonru-exists
  - non-ce-bcs-has-robust-approximate-energy-gap
  - boolean-predicate-central-phase-word
  - finite-packet-central-sign-cannot-enforce-nonlinear-support
  - bcs-projective-kernel-phase-compilation
  - gowers-hatami-finite-group-hs-stability
---

Use the finite `2`-group word as the scalar phase register and the engineered
tracial model for perfect completeness.  Finite-group flexible stability
controls approximate packet tables after the full compiler has excluded the
exact unwanted marked sectors identified by
`finite-packet-central-sign-cannot-enforce-nonlinear-support`; stability alone
cannot exclude them.  The robust non-RU energy theorem then gives
finite-dimensional soundness, while the full tracial model certifies that the
phase is not killed by normal closure.  These are exactly the three clauses of
the target toric game.

This route counts violations rather than excluding forbidden selector
characters, so it does not invoke the finite-selector induction barrier.
