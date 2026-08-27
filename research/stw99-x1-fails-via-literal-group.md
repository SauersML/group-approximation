---
rg: 2
id: stw99-x1-fails-via-literal-group
kind: route
title: Factorization property of the literal group plus its non-quasidiagonal trace refutes Problem X(1)
target: stw99-problem-x1-fails-on-full-group-algebras
requires: [literal-group-factorization-property, literal-canonical-trace-hyperlinear-not-quasidiagonal]
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

If `E` has Kirchberg's factorization property then, by Brown's Theorem 4.1.9
(N. P. Brown, *Invariant means and finite representation theory of C\*-algebras*, Mem. Amer. Math. Soc. 184 (2006), no. 865), the canonical trace `τ_E` on `C*(E)` is an amenable trace.  The
second premise says `τ_E` is not a quasidiagonal trace.  So `τ_E` is an
amenable trace that is not quasidiagonal, which is the target with `G = E`.

Nothing else is used.  The premise
`literal-canonical-trace-hyperlinear-not-quasidiagonal` is established in
Lean; the factorization-property premise is the only open leaf.

**Formalized:** `NinetyNineProblems.not_problemX1Statement_of_literalFactorizationProperty :
LiteralFactorizationProperty → ¬ ProblemX1Statement` and its contrapositive
`not_literalFactorizationProperty_of_problemX1Statement` (`GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean`, 2dbea8f73).
The Lean hypothesis is exactly the open leaf.
