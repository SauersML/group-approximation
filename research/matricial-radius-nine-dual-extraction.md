---
rg: 2
id: matricial-radius-nine-dual-extraction
kind: claim
title: A dimension-sensitive hierarchy extracts a rational radius-nine atlas separator
distinct_from:
  atlas-radius-nine-trace-separator: that is the mathematical inequality; this asks for a finite, replayable dual proof in a specified matricial positivity calculus.
  tracial-npa-cannot-separate-canonical-trace: that excludes the standard tracial hierarchy; this requires matrix-specific identities or exterior-power and invariant-theory certificates unavailable in arbitrary tracial von Neumann algebras.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Construct a nested computational hierarchy over the radius-nine atlas trace
word orbit basis whose dual certificates are:

1. rational and exactly replayable;
2. sound in every matrix size after adding the fixed atlas relator-energy
   penalty; and
3. not sound in arbitrary tracial von Neumann algebras, because the proof
   explicitly uses finite-dimensional invariant theory, exterior powers, or a
   dimension-indexed argument subsequently made uniform in `n`.

At some finite level the dual optimum supplies coefficients `a_w,C,c` with
the signs required by `atlas-radius-nine-trace-separator`.  Direct finite-size
matrix optimization may seed the candidate, but is not the certificate.

The campaign has a hard stopping rule in both directions: a replayed rational
dual closes the claim; a canonical-trace-feasible dual reveals that the
implementation has accidentally reverted to the forbidden tracial NPA cone.

## Attempts

- Enumerate cyclic radius-nine word orbits and use finite-size unitary
  optimization only to guess a sparse coefficient vector.
- Rationally reconstruct it, then seek a uniform proof from Procesi trace
  identities, exterior powers, and Schur-complement inequalities.
- Standard tracial moment matrices are excluded. If canonical atlas moments
  remain feasible in the implemented cone, that run is diagnostic only.
