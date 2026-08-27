---
rg: 2
id: stw99-vii-implies-ix1
kind: route
title: A faithful trace forces stable finiteness
target: stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal
requires: [stw99-problem-vii-blackadar-kirchberg]
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/StablyFinite.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

If `τ` is a faithful tracial state on `A` and `v ∈ M_n(A)` satisfies
`v*v = 1`, then `p = 1 − vv*` is a projection with `τₙ(p) = τₙ(1) − τₙ(v*v) = 0`
for the amplified faithful trace `τₙ`, so `p = 0`.  Hence `M_n(A)` is finite
for every `n`, i.e. `A` is stably finite, and Problem VII applies.

Formalizable over `FaithfulTracialState` with a definition of stable
finiteness in matrix amplifications; a Lean module for this route is being
authored under `GroupApproximation/Manuscript/NinetyNineProblems/`.

**Formalized.**  `GroupApproximation/Manuscript/NinetyNineProblems/StablyFinite.lean`:
`isStablyFiniteCStarAlgebra_of_faithfulTracialState` (assembled from the
repository's `FaithfulTracialState.matrix` amplification and
`mul_star_eq_one_of_star_mul_eq_one`), the two named statements
`ProblemVIIStatement` and `ProblemIX1Statement`, and
`problemIX1Statement_of_problemVIIStatement`.  Axiom-clean; landed b6103bc6f.
