---
rg: 2
id: stw99-x1-fails-via-literal-group
kind: route
title: Factorization property of the literal group plus its non-quasidiagonal trace refutes Problem X(1)
target: stw99-problem-x1-fails-on-full-group-algebras
requires: [literal-group-factorization-property, literal-canonical-trace-hyperlinear-not-quasidiagonal]
artifacts:
  - GroupApproximation/Sofic/ResidualFinitePacket.lean
  - GroupApproximation/Analysis/QuasiRegularCompression.lean
  - GroupApproximation/Analysis/AmenableTraceGeneratorDense.lean
  - GroupApproximation/Analysis/LocallyRFByIntFactorization.lean
  - GroupApproximation/Analysis/AmenableTraceHyperlinear.lean
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**ROUTE ESTABLISHED AND FORMALIZED.**  Both premises are Lean theorems; the
literal group supplies an amenable non-quasidiagonal maximal canonical trace.

If `E` has Kirchberg's factorization property then, by Brown's Theorem 4.1.9
(N. P. Brown, *Invariant means and finite representation theory of C\*-algebras*, Mem. Amer. Math. Soc. 184 (2006), no. 865), the canonical trace `τ_E` on `C*(E)` is an amenable trace.  The
second premise says `τ_E` is not a quasidiagonal trace.  So `τ_E` is an
amenable trace that is not quasidiagonal, which is the target with `G = E`.

Nothing else is used.  The premise
`literal-canonical-trace-hyperlinear-not-quasidiagonal` is established in
Lean; the factorization-property premise is now established.

**Formalized:**
`NinetyNineProblems.literalFactorizationProperty :
LiteralFactorizationProperty` discharges the premise from the stable-letter
splitting and local residual finiteness of its kernel.  The reusable bridge is
`not_problemX1Statement_of_literalFactorizationProperty`; composing them gives
the unconditional, axiom-clean theorem
`NinetyNineProblems.not_problemX1Statement : ¬ ProblemX1Statement` in
`GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean`.

Side fact now machine-checked: the premise already implies `E` hyperlinear
(Brown 3.1.7, a theorem in `GroupApproximation/Analysis/AmenableTraceHyperlinear.lean`), consistent
with soficity; the content of the premise beyond soficity is exactly the
u.c.p. lifting.
