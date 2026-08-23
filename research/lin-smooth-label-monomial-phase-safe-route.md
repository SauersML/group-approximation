---
rg: 2
id: lin-smooth-label-monomial-phase-safe-route
kind: route
title: Use smooth-label projective colors as the narrowed monomial compiler input
target: phase-safe-toric-gap-game-exists
requires:
  - lin-gap-smooth-label-cover-projective-color-game
  - smooth-label-cover-edges-are-finite-phase-projective-color
  - monomial-game-pair-compatibility-is-projective-color-rigid
  - finite-phase-monomial-game-algebra-dictionary
  - harris-circulant-one-matrix-compiler-forces-affine-support
  - smooth-label-cover-gap-full-corner-monomial-realization
  - monomial-gap-phase-safe-toric-groupification
artifacts:
  - research/artifacts/cmps-smooth-label-monomial-audit-2026-08-23.md
---

The Lin--CMPS hybrid reduction gives a fixed finite smooth-label-cover game
with a perfect commuting strategy and a finite-dimensional gap.  Unlike a
general BCS predicate, each of its edge relations is already equality of one
finite projective color.  Solve
`smooth-label-cover-gap-full-corner-monomial-realization` to package those
local color tests and the vertex PVMs into one finite-phase monomial matrix
pair without changing the trace or `R^omega` representation spaces.

The finite-phase dictionary then gives a separated monomial linking algebra.
Apply `monomial-gap-phase-safe-toric-groupification` to retain its Fourier
phase projections while proving that the scalar phase survives normal
closure.  This produces the phase-safe toric gap requested by the target.

The two open requirements are logically separate.  Edgewise color equality
does not prove a full-corner square completion, and a perfect tracial
monomial algebra does not by itself prove phase survival in its group
normal quotient.
