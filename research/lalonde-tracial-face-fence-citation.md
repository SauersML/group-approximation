---
rg: 2
id: lalonde-tracial-face-fence-citation
kind: route
title: Import Lalonde's tracial-NPA separation
target: lalonde-perfect-fd-strategy-has-no-tracial-game-state
requires: []
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

## Source theorem

Lalonde, arXiv:2608.05378v1, Theorem 1.1 constructs the bipartite game
`G_(4,3,6,6)` with a perfect finite-dimensional strategy in local
dimension six but no perfect strategy using a maximally entangled state.
Section 4.2 writes the latter condition as existence of a tracial state on
the square-root effect algebra satisfying the POVM and cross-commutation
relations and annihilating every losing product `E_a^x F_b^y`.

A strengthened level-four tracial-NPA relaxation is infeasible.  The paper
extracts a rational infeasibility certificate and formalizes the
nonexistence theorem in Lean.  Hence the perfect finite vector-state
strategy cannot be replaced, for this game, by a perfect state on that
tracial face.  This is exactly the fence asserted by the target claim.
