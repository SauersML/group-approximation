---
rg: 2
id: nonsingular-radical-conservation-proof
kind: route
title: Lift coefficients, solve coordinatewise, and compare all homomorphism kernels
target: nonsingular-adjunction-preserves-approximation-radicals
requires:
  - nonsingular-equations-preserve-matrix-certificates
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

Lift the finitely many coefficients into the unitary product. The
prerequisite supplies an exact root in each coordinate, so the root sequence
solves the equation in the quotient. Its universal property extends every
coefficient-group homomorphism into that same target. Section 3 also checks
unitary lifting for norm C-star coronas by polar decomposition.

Restriction gives one radical inclusion. For the other, extend any map
detecting an old element; its extension still detects that element's image.
This proves the two pullback equalities and the common-radical bound on the
coefficient kernel. Successive extensions into one fixed target and the
direct-limit universal property prove the triangular version in Section 4.
