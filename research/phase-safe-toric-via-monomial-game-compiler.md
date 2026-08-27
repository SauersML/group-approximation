---
rg: 2
id: phase-safe-toric-via-monomial-game-compiler
kind: route
title: Pass the non-CE game through Harris, monomial linking syntax, and phase-safe groupification
target: phase-safe-toric-gap-game-exists
requires:
  - mipstar-bcs-tracial-nonru-exists
  - harris-bisynchronous-game-algebra-preservation
  - finite-phase-monomial-game-algebra-dictionary
  - monomial-game-pair-compatibility-is-projective-color-rigid
  - finite-dimensional-kplus-does-not-factor-through-hinfinityplus
  - finite-unitary-canonical-trace-span-no-go
  - elementary-abelian-harris-lift-compiles-bcs-consistency
  - harris-circulant-one-matrix-compiler-forces-affine-support
  - quadratic-pair-incidence-monomial-entry-forces-commutation
  - oracular-commutation-quotient-preserves-tracial-nonru
  - bisynchronous-to-monomial-game-algebra-compiler
  - monomial-gap-phase-safe-toric-groupification
artifacts:
  - research/artifacts/harris-monomial-compiler-first-pass-2026-08-22.md
---

Start with the fixed synchronous game algebra having a tracial state and no
homomorphism into `R^omega`.  Harris replaces it by an equal-size
bisynchronous game without changing the algebra.  The monomial compiler then
realizes that algebra, or a trace-preserving full corner of it, as one finite
`s`-monomial matrix-pair algebra.  By the finite-phase monomial dictionary,
the resulting game has perfect commuting play and no perfect `qa` play.

Finally apply the phase-safe toric groupification to retain this gap while
certifying survival of the finite scalar phase under normal closure.  The
output satisfies every clause of `phase-safe-toric-gap-game-exists`, after
which the already established toric endpoint gives the nonhyperlinear group.

The no-go inputs delimit rather than close the two open compiler gates:
direct monomial compatibility is projective-color rigid, finite-dimensional
weak quantum reflections need not become strong, and an ordinary finite
unitary packet cannot both span its matrix block and carry canonical group
trace.  Hence a surviving construction must use a genuine auxiliary/full-
corner monomial gadget and protect its scalar phase through the normal
quotient.
